"""Collapse near-duplicate theorems into supernodes, and score the supernodes.

Every theorem here is a tautology, so "logically equivalent" would put all of
them in one supernode. Supernodes are instead built from three syntactic
relations, each level merging whole supernodes of the level below:

  level 1  redundancy: a theorem joins a more general theorem that is no longer
           to prove (`p -> (p -> p)` joins ax-1). Same as the existing filter.
  level 2  + weakening: drop leading antecedents that are fresh variables, so
           `q -> A` ("A with a dummy hypothesis") joins A. Puts set.mm's ax1w
           with ax-1 and idd with `p -> p`.
  level 3  + exchange: hypothesis order is ignored (`p -> (q -> r)` joins
           `q -> (p -> r)`), and fresh-variable hypotheses anywhere are dropped.
           Merges Principia's two "Syll" theorems (*2.05, *2.06). It also merges
           ax-1 `p -> (q -> p)` with `p -> p`.

A supernode's representative is its most general, cheapest member: at level 1
the theorem every member is an instance of; above that, the member with the
shortest proof, then the smallest statement, then the most distinct variables
(merging two variables keeps the size but loses generality), then the lowest
id. The representative's id is the supernode id.

Scores at each level treat the library as the set of supernodes, and a
supernode's proof length as the shortest proof of any member:

  gain      Make every member free, re-solve; saving = total drop in proof length
            over the *other* supernodes; gain = saving - proof length of the supernode.
  knockout  Forbid every member, re-solve; total rise over the other supernodes
            (a supernode left with no proof inside the horizon counts as N + 1).
  lost      Other supernodes left with no proof inside the horizon.
  affected  Other supernodes whose proof gets longer at all.

Banning a whole supernode stops near-variants from standing in for each other,
which is what single-theorem knockout could not do.

Usage (after logicgraph.hyperscores):
    python -m logicgraph.supernodes data/gen/luk21 [--candidate-slack 6]
"""

from __future__ import annotations

import argparse
import csv
import itertools
import sys
import time
from pathlib import Path

import numpy as np

from .formula import canon, parse_polish, to_polish, to_str, variables
from .hyperscores import Hypergraph

LEVELS = (1, 2, 3)
LEVEL_NAMES = {1: "redundancy", 2: "+ weakening", 3: "+ exchange"}
MAX_PERMUTE = 6          # antecedents; beyond this, exchange falls back to the formula's own order


def _split(t) -> tuple[list, object]:
    """`A1 -> (A2 -> ... -> C)` as ([A1, A2, ...], C)."""
    ants = []
    while not isinstance(t, int) and len(t) == 2:
        ants.append(t[0])
        t = t[1]
    return ants, t


def _build(ants: list, c):
    for a in reversed(ants):
        c = (a, c)
    return c


def weakening_key(t) -> str:
    """Canonical form after dropping leading antecedents that are fresh variables."""
    while not isinstance(t, int) and len(t) == 2 and isinstance(t[0], int) and t[0] not in variables(t[1]):
        t = t[1]
    return to_polish(canon(t))


def exchange_key(t) -> str:
    """Canonical form ignoring hypothesis order and fresh-variable hypotheses anywhere."""
    ants, c = _split(t)
    changed = True
    while changed:
        changed = False
        for k, a in enumerate(ants):
            rest = ants[:k] + ants[k + 1:]
            if isinstance(a, int) and a not in variables(_build(rest, c)):
                ants, changed = rest, True
                break
    if len(ants) > MAX_PERMUTE:
        return to_polish(canon(_build(ants, c)))
    return min(to_polish(canon(_build(list(p), c))) for p in itertools.permutations(ants))


def build_levels(formulas: dict[int, object], steps: dict[int, int], sizes: dict[int, int],
                 subsumed_by: dict[int, int]) -> dict[int, dict[int, int]]:
    """Supernode id (= representative id) of every theorem, per level.

    `formulas`, `steps` and `sizes` cover the library; `subsumed_by` maps each
    redundant theorem to the theorem it is an instance of.
    """
    n_vars = {i: len(variables(t)) for i, t in formulas.items()}
    order = lambda i: (steps[i], sizes[i], -n_vars[i], i)

    def root(i: int) -> int:
        while i in subsumed_by:
            i = subsumed_by[i]
        return i

    level: dict[int, dict[int, int]] = {1: {i: root(i) for i in formulas}}

    for k, key_fn in ((2, weakening_key), (3, exchange_key)):
        prev = level[k - 1]
        merged: dict[str, list[int]] = {}
        for r in set(prev.values()):                      # key each lower-level representative
            merged.setdefault(key_fn(formulas[r]), []).append(r)
        rep_of_prev = {r: min(rs, key=order) for rs in merged.values() for r in rs}
        level[k] = {i: rep_of_prev[prev[i]] for i in formulas}
    return level


class SupernodeScorer:
    """Scores supernodes on the hypergraph, with supernode length = min over members."""

    def __init__(self, g: Hypergraph, assign: dict[int, int]):
        self.g = g
        ids = np.array(sorted(assign), dtype=np.int64)
        cls = np.array([assign[i] for i in ids.tolist()], dtype=np.int64)
        order = np.argsort(cls, kind="stable")
        self.members = ids[order]
        self.cls = cls[order]
        self.starts = np.flatnonzero(np.r_[True, self.cls[1:] != self.cls[:-1]])
        self.reps = self.cls[self.starts]
        self.index = {int(r): k for k, r in enumerate(self.reps.tolist())}
        self.base = self.lengths(g.L0)

    def lengths(self, L: np.ndarray) -> np.ndarray:
        return np.minimum.reduceat(L[self.members].astype(np.int64), self.starts)

    def members_of(self, rep: int) -> np.ndarray:
        k = self.index[rep]
        end = self.starts[k + 1] if k + 1 < len(self.starts) else len(self.members)
        return self.members[self.starts[k]:end]

    def score(self, rep: int) -> dict:
        g, k = self.g, self.index[rep]
        others = np.ones(len(self.reps), dtype=bool)
        others[k] = False
        vs = self.members_of(rep)
        base = self.base[others]
        _, Ln = g.resolve(vs, "name")
        saving = int((base - self.lengths(Ln)[others]).sum())
        _, Lb = g.resolve(vs, "ban")
        after_raw = self.lengths(Lb)[others]
        after = np.minimum(after_raw, g.N + 1)
        return {
            "saving": saving,
            "gain": saving - int(self.base[k]),
            "knockout": int((after - base).sum()),
            "lost": int((after_raw > g.N).sum()),
            "affected": int((after > base).sum()),
        }


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run", type=Path, help="directory with theorems.csv, derivations.csv, scores.csv")
    ap.add_argument("--candidate-slack", type=int, default=6,
                    help="score supernodes whose proof length is <= N - this")
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr)
    t0 = time.time()

    g = Hypergraph.load(args.run)
    with open(args.run / "scores.csv", newline="") as f:
        sc = list(csv.DictReader(f))
    with open(args.run / "theorems.csv", newline="") as f:
        th = [r for r, s in zip(csv.DictReader(f), sc) if s["is_target"] == "1" or s["subsumed_by"] != ""]
    # The library: every theorem short enough to be a target, redundant instances included.
    lib = {int(r["id"]): r for r in th}
    subsumed_by = {int(s["id"]): int(s["subsumed_by"]) for s in sc if s["subsumed_by"] != ""}
    formulas = {i: parse_polish(r["formula"]) for i, r in lib.items()}
    steps = {i: int(r["min_steps"]) for i, r in lib.items()}
    sizes = {i: int(r["size"]) for i, r in lib.items()}
    levels = build_levels(formulas, steps, sizes, subsumed_by)
    log(f"library: {len(lib)} theorems [{time.time() - t0:.1f}s]")
    for k in LEVELS:
        log(f"  level {k} ({LEVEL_NAMES[k]}): {len(set(levels[k].values()))} supernodes")

    with open(args.run / "supernodes.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", *(f"level{k}" for k in LEVELS)])
        for i in sorted(lib):
            w.writerow([i, *(levels[k][i] for k in LEVELS)])

    cols = ["saving", "gain", "knockout", "lost", "affected"]
    with open(args.run / "supernode_scores.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["level", "supernode", "formula", "readable", "n_members", "n_named", "names",
                    "min_steps", "rep_size", "is_candidate", *cols])
        for k in LEVELS:
            scorer = SupernodeScorer(g, levels[k])
            limit = g.N - args.candidate_slack
            n_scored = 0
            for rep in scorer.reps.tolist():
                ms = scorer.members_of(rep).tolist()
                names = sorted({x for m in ms for x in (lib[m]["pm"], lib[m]["setmm"]) if x})
                cand = int(scorer.base[scorer.index[rep]]) <= limit
                s = scorer.score(rep) if cand else None
                n_scored += cand
                w.writerow([k, rep, lib[rep]["formula"], lib[rep]["readable"], len(ms),
                            sum(1 for m in ms if lib[m]["pm"] or lib[m]["setmm"]), " | ".join(names),
                            lib[rep]["min_steps"], lib[rep]["size"], int(cand),
                            *([s[c] for c in cols] if s else [""] * len(cols))])
            log(f"  level {k}: scored {n_scored} candidate supernodes ({time.time() - t0:.0f}s)")
    log(f"-> {args.run / 'supernodes.csv'}, {args.run / 'supernode_scores.csv'} ({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()
