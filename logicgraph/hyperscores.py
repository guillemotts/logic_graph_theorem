"""Importance scores on the generated AND-OR hypergraph.

A theorem can have many derivations, so "what if this lemma were free?" and
"what if this lemma were forbidden?" have real answers here (they did not on
set.mm, where each theorem has exactly one proof).

Let L(t) be the length of the shortest D-proof of t, N the generation horizon,
and the *targets* the theorems with L(t) <= N - slack (our "library").

Redundant theorems (instances of another theorem that is no longer to prove,
see `subsumption.py`) are left out of the targets and the candidates. They stay
in the graph as possible proof steps.

  deep       L(t) / size(t): short to state, long to prove.
  gain       Naming gain. Make v cost 1 step, as if it were an axiom, and
             re-solve. saving = sum over targets of the drop in L;
             gain = saving - L(v) (the cost of proving v once).
             A lower bound: proofs whose full expansion exceeds N are not seen.
  knockout   Forbid v and re-solve. knockout = sum over targets of the rise in
             L, counting a target with no proof left inside the horizon as N + 1.
  lost       Number of targets with no proof left inside the horizon
             ("unavoidable within the horizon").
  affected   Number of targets whose shortest proof gets longer at all.

Exactness: the derivations on file are those with L(major) + L(minor) + 1 <= N,
so a re-solved length is exact whenever it is <= N, and anything above N is
truly above N.

Baselines for comparison: size, min_steps, n_derivations, n_uses, and
min_uses (targets that have a shortest derivation using v directly).

Usage:
    python -m logicgraph.hyperscores data/gen/luk21 [--slack 4] [--candidate-slack 6]
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

import numpy as np

from .formula import parse_polish
from .subsumption import redundant

BIG = 1 << 28      # "no proof"; BIG + BIG + 1 still fits in int32


def _gather(start: np.ndarray, nodes: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Positions covered by the CSR ranges of `nodes`, and the size of each range."""
    counts = start[nodes + 1] - start[nodes]
    total = int(counts.sum())
    offsets = np.repeat(start[nodes] - (np.cumsum(counts) - counts), counts)
    return np.arange(total, dtype=np.int64) + offsets, counts


class Hypergraph:
    def __init__(self, steps: np.ndarray, n_axioms: int, conc: np.ndarray, maj: np.ndarray,
                 mnr: np.ndarray, max_steps: int):
        self.n = n = len(steps)
        self.L0 = steps.astype(np.int32)
        self.n_axioms = n_axioms
        self.N = max_steps
        # Derivations sorted by conclusion; der_start[c]..der_start[c+1] are those concluding c.
        order = np.argsort(conc, kind="stable")
        self.conc, self.maj, self.mnr = conc[order], maj[order], mnr[order]
        self.der_start = np.searchsorted(self.conc, np.arange(n + 1)).astype(np.int64)
        # For each theorem, the derivations that use it as a premise.
        m = len(self.conc)
        prem = np.concatenate([self.maj, self.mnr])
        der = np.concatenate([np.arange(m), np.arange(m)])
        by_prem = np.argsort(prem, kind="stable")
        self.use_der = der[by_prem]
        self.use_start = np.searchsorted(prem[by_prem], np.arange(n + 1)).astype(np.int64)
        # "Tight" derivations achieve the shortest length of their conclusion. A theorem can
        # only get longer when a tight derivation of it loses a premise, so the tight links
        # (premise -> conclusion) bound what a ban can affect.
        tight = self.L0[self.maj] + self.L0[self.mnr] + 1 == self.L0[self.conc]
        pairs = np.unique(np.concatenate([
            np.stack([self.maj[tight], self.conc[tight]], axis=1),
            np.stack([self.mnr[tight], self.conc[tight]], axis=1)]), axis=0)
        self.tight_child = pairs[:, 1].astype(np.int64)
        self.tight_start = np.searchsorted(pairs[:, 0], np.arange(n + 1)).astype(np.int64)

    @classmethod
    def load(cls, run: Path) -> "Hypergraph":
        meta = json.loads((run / "meta.json").read_text())
        with open(run / "theorems.csv", newline="") as f:
            steps = np.array([int(r["min_steps"]) for r in csv.DictReader(f)], dtype=np.int32)
        d = np.loadtxt(run / "derivations.csv", delimiter=",", skiprows=1, dtype=np.int32)
        return cls(steps, meta["n_axioms"], d[:, 0], d[:, 1], d[:, 2], meta["max_steps"])

    # ---------------------------------------------------------------- solving

    def exposed(self, v) -> np.ndarray:
        """Theorems (outside v) reachable from v through tight derivations, sorted.

        `v` is one theorem id or an array of them. Any theorem outside this set
        keeps a shortest derivation that involves none of v, so banning v cannot
        change its length.
        """
        vs = np.atleast_1d(np.asarray(v, dtype=np.int64))
        seen = np.zeros(self.n, dtype=bool)
        seen[vs] = True
        frontier = vs
        while len(frontier):
            pos, _ = _gather(self.tight_start, frontier)
            kids = self.tight_child[pos]
            frontier = np.unique(kids[~seen[kids]])
            seen[frontier] = True
        seen[vs] = False
        return np.flatnonzero(seen)

    def resolve(self, v, mode: str) -> tuple[np.ndarray, np.ndarray]:
        """Shortest lengths with v forbidden (mode="ban") or free (mode="name").

        `v` is one theorem id or an array of them (a whole supernode). Returns
        (nodes, L): L is the full length array and `nodes` the theorems outside v
        whose length may differ from L0. Lengths above N mean "no proof inside
        the horizon".
        """
        vs = np.atleast_1d(np.asarray(v, dtype=np.int64))
        L = self.L0.copy()
        if mode == "ban":
            nodes = self.exposed(vs)
            L[vs] = BIG
            if len(nodes) == 0:
                return nodes, L
            L[nodes] = BIG
            idx, counts = _gather(self.der_start, nodes)
            maj, mnr = self.maj[idx], self.mnr[idx]
            starts = np.cumsum(counts) - counts
            while True:
                new = np.minimum.reduceat(L[maj] + L[mnr] + 1, starts)
                np.minimum(new, L[nodes], out=new)
                if np.array_equal(new, L[nodes]):
                    return nodes, L
                L[nodes] = new
        if mode == "name":
            L[vs] = 1
            touched = np.zeros(self.n, dtype=bool)
            changed = vs
            while len(changed):
                # Only derivations that use a theorem that just got shorter can improve anything.
                pos, _ = _gather(self.use_start, changed)
                idx = np.unique(self.use_der[pos])
                c = self.conc[idx]
                cand = L[self.maj[idx]] + L[self.mnr[idx]] + 1
                better = cand < L[c]
                c, cand = c[better], cand[better]
                np.minimum.at(L, c, cand)
                changed = np.unique(c)
                touched[changed] = True
            return np.flatnonzero(touched), L
        raise ValueError(mode)

    def solve_reference(self, banned: set[int] = frozenset(), free: set[int] = frozenset()) -> list[int]:
        """Slow, obviously-correct solver over the whole graph, for tests."""
        L = [BIG] * self.n
        for a in range(self.n_axioms):
            L[a] = 1
        for v in free:
            L[v] = 1
        for v in banned:
            L[v] = BIG
        changed = True
        while changed:
            changed = False
            for c, a, b in zip(self.conc.tolist(), self.maj.tolist(), self.mnr.tolist()):
                if c in banned or c in free or c < self.n_axioms:
                    continue
                x = L[a] + L[b] + 1
                if x < L[c]:
                    L[c] = x
                    changed = True
        return [min(x, BIG) for x in L]

    # ---------------------------------------------------------------- scores

    def score(self, v: int, targets: np.ndarray) -> dict:
        """gain / knockout scores for one candidate. `targets` is a boolean mask."""
        nodes, Ln = self.resolve(v, "name")
        t = nodes[targets[nodes]]
        saving = int((self.L0[t].astype(np.int64) - Ln[t]).sum())
        nodes, Lb = self.resolve(v, "ban")
        t = nodes[targets[nodes]]
        base = self.L0[t].astype(np.int64)
        after = np.minimum(Lb[t], self.N + 1).astype(np.int64)
        return {
            "saving": saving,
            "gain": saving - int(self.L0[v]),
            "knockout": int((after - base).sum()),
            "lost": int((Lb[t] > self.N).sum()),
            "affected": int((after > base).sum()),
        }

    def min_uses(self, targets: np.ndarray) -> np.ndarray:
        """For each theorem, the number of targets with a shortest derivation using it directly."""
        tight = (self.L0[self.maj] + self.L0[self.mnr] + 1 == self.L0[self.conc]) & targets[self.conc]
        pairs = np.unique(np.concatenate([
            np.stack([self.maj[tight], self.conc[tight]], axis=1),
            np.stack([self.mnr[tight], self.conc[tight]], axis=1)]), axis=0)
        return np.bincount(pairs[:, 0], minlength=self.n)


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run", type=Path, help="directory written by logicgraph.generate")
    ap.add_argument("--slack", type=int, default=4, help="targets are theorems with L <= N - slack")
    ap.add_argument("--candidate-slack", type=int, default=6, help="candidates are theorems with L <= N - this")
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr)
    t0 = time.time()

    g = Hypergraph.load(args.run)
    with open(args.run / "theorems.csv", newline="") as f:
        rows = list(csv.DictReader(f))
    log(f"{g.n} theorems, {len(g.conc)} derivations (horizon {g.N}) [loaded in {time.time() - t0:.1f}s]")

    # Redundancy among the theorems short enough to be targets.
    in_range = np.flatnonzero(g.L0 <= g.N - args.slack)
    assert (in_range == np.arange(len(in_range))).all(), "theorem ids must be ordered by proof length"
    red = redundant([parse_polish(rows[i]["formula"]) for i in in_range], g.L0[in_range].tolist())
    subsumed_by = {i: j for i, j in enumerate(red) if j is not None}
    keep = np.ones(g.n, dtype=bool)
    keep[list(subsumed_by)] = False
    targets = (g.L0 <= g.N - args.slack) & keep
    cand = np.flatnonzero((g.L0 <= g.N - args.candidate_slack) & keep)
    log(f"{len(in_range)} theorems with L<={g.N - args.slack}: {len(subsumed_by)} redundant "
        f"({100 * len(subsumed_by) / len(in_range):.0f}%), {int(targets.sum())} targets; "
        f"{len(cand)} candidates (L<={g.N - args.candidate_slack}) [{time.time() - t0:.1f}s]")

    muses = g.min_uses(targets)
    scores: dict[int, dict] = {}
    for k, v in enumerate(cand.tolist()):
        scores[v] = g.score(v, targets)
        if (k + 1) % 1000 == 0:
            log(f"  scored {k + 1}/{len(cand)} ({time.time() - t0:.0f}s)")

    cols = ["saving", "gain", "knockout", "lost", "affected"]
    with open(args.run / "scores.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "min_steps", "size", "deep", "n_derivations", "n_uses", "min_uses",
                    "subsumed_by", "is_target", "is_candidate", *cols])
        for i, r in enumerate(rows):
            s = scores.get(i)
            w.writerow([i, r["min_steps"], r["size"], f"{int(r['min_steps']) / int(r['size']):.4f}",
                        r["n_derivations"], r["n_uses"], int(muses[i]), subsumed_by.get(i, ""),
                        int(targets[i]), int(s is not None),
                        *([s[c] for c in cols] if s else [""] * len(cols))])

    n_targets = int(targets.sum()) - g.n_axioms
    log(f"\nWhat each axiom buys (targets with no proof left inside the horizon, of {n_targets}):")
    for a in range(g.n_axioms):
        log(f"  without axiom {a + 1} ({rows[a]['readable']}): {scores[a]['lost']} lost "
            f"({100 * scores[a]['lost'] / n_targets:.1f}%)")
    log(f"scores for {len(cand)} candidates -> {args.run / 'scores.csv'} ({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()
