"""The lemma contest: can an algorithm pick a better lemma library than the humans did?

A *lemma library* S is a set of theorems that, once named, each count as a single
step. The total cost of a library is

    cost(S) = sum over v in S of L(v)  +  sum over library theorems t of L_S(t)

where L(v) is what proving v once costs (its shortest proof from the axioms) and
L_S(t) is the shortest proof of t when the lemmas in S are free. Lower is better;
saving(S) = cost({}) - cost(S).

Contestants, all of the same size k as the human set H:

  greedy   add, k times, the candidate that lowers the cost most
  top-k    the k candidates with the highest naming gain on their own
  human    H: the candidates that carry a human name (Principia or set.mm),
           and the Principia-only subset (set.mm's names were chosen in this
           exact axiom system; Principia's were not)
  random   sets that match H theorem for theorem in proof length and
           statement size (2,000 draws)

Two cost measures (question 2: is tree size doing the work?):

  tree     L = number of steps in the proof written out as a tree. A lemma used
           m times in one proof is paid for m times. This is what the naming
           gain in hyperscores.py uses.
  dag      D = number of distinct theorems in the proof (each step counted once,
           however often it is reused). Finding the smallest DAG proof is hard,
           so D is computed by dynamic programming: each theorem keeps the
           smallest set of steps found so far, D(c) = min over derivations
           (a, b) -> c of |steps(a) ∪ steps(b) ∪ {c}|, relaxed to a fixed point.
           That gives an upper bound on the true smallest DAG size. It is
           computed over the theorems with L <= N - slack (the targets' range).

The report also recomputes naming gain under DAG size for every candidate and
asks again whether it picks out the human names (same AUC and matched AUC as
validate.py).

Usage:
    python -m logicgraph.lemma_contest data/gen/luk21
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

import numpy as np

from .hyperscores import Hypergraph, _gather
from .validate import evaluate, fmt


# ------------------------------------------------------------------ tree cost

class TreeCost:
    """Tree size with a set of free lemmas, built on Hypergraph's propagation."""

    def __init__(self, g: Hypergraph, targets: np.ndarray):
        self.g, self.targets = g, np.flatnonzero(targets)
        self.base = g.L0.copy()

    def name(self, L: np.ndarray, vs) -> np.ndarray:
        """Lengths when the lemmas vs become free, starting from lengths L (already with
        some lemmas free). Only derivations using something that got shorter are revisited."""
        g = self.g
        L = L.copy()
        vs = np.atleast_1d(np.asarray(vs, dtype=np.int64))
        vs = vs[L[vs] > 1]
        L[vs] = 1
        changed = vs
        while len(changed):
            pos, _ = _gather(g.use_start, changed)
            idx = np.unique(g.use_der[pos])
            c = g.conc[idx]
            cand = L[g.maj[idx]] + L[g.mnr[idx]] + 1
            better = cand < L[c]
            c, cand = c[better], cand[better]
            np.minimum.at(L, c, cand)
            changed = np.unique(c)
        return L

    def total(self, L: np.ndarray) -> int:
        return int(L[self.targets].astype(np.int64).sum())

    def price(self, v: int) -> int:
        return int(self.base[v])


# ------------------------------------------------------------------ DAG cost

class DagCost:
    """Distinct-step (DAG) size with a set of free lemmas, over a universe of theorems.

    State is a list `C` of frozensets: C[t] is the set of distinct theorems in the
    best proof of t found so far (t included). Free lemmas have C[v] = {v}.
    """

    def __init__(self, g: Hypergraph, targets: np.ndarray, universe: np.ndarray):
        self.g = g
        self.targets = np.flatnonzero(targets)
        U = universe
        keep = U[g.conc] & U[g.maj] & U[g.mnr] & (g.conc != g.maj) & (g.conc != g.mnr)
        self.conc, self.maj, self.mnr = g.conc[keep].tolist(), g.maj[keep].tolist(), g.mnr[keep].tolist()
        n = g.n
        self.uses: list[list[int]] = [[] for _ in range(n)]
        for d, (a, b) in enumerate(zip(self.maj, self.mnr)):
            self.uses[a].append(d)
            if b != a:
                self.uses[b].append(d)
        by_conc: list[list[int]] = [[] for _ in range(n)]
        for d, c in enumerate(self.conc):
            by_conc[c].append(d)
        EMPTY = None
        C: list = [EMPTY] * n
        for a in range(g.n_axioms):
            C[a] = frozenset((a,))
        # First pass in id order (ids are ordered by tree length, so every tight
        # derivation's premises come first), then relax to a fixed point.
        order = [int(i) for i in np.flatnonzero(U) if i >= g.n_axioms]
        for _ in range(50):
            changed = 0
            for c in order:
                best = C[c]
                for d in by_conc[c]:
                    A, B = C[self.maj[d]], C[self.mnr[d]]
                    if A is None or B is None:
                        continue
                    s = A | B
                    if best is None or len(s) + 1 < len(best):
                        best = s | {c}
                if best is not C[c]:
                    C[c] = best
                    changed += 1
            if not changed:
                break
        self.base = C
        self.unreached = sum(1 for i in order if C[i] is None)

    def name(self, C: list, vs) -> list:
        """Closures when the lemmas vs become free (copy-on-write: returns a new list
        only if something changed)."""
        vs = [int(v) for v in np.atleast_1d(vs) if len(C[int(v)]) > 1]
        if not vs:
            return C
        C = list(C)
        frontier = []
        for v in vs:
            C[v] = frozenset((v,))
            frontier.append(v)
        while frontier:
            nxt = set()
            for x in frontier:
                for d in self.uses[x]:
                    c, A, B = self.conc[d], C[self.maj[d]], C[self.mnr[d]]
                    if A is None or B is None or len(C[c]) == 1:
                        continue
                    s = A | B
                    if len(s) + 1 < len(C[c]):
                        C[c] = s | {c}
                        nxt.add(c)
            frontier = list(nxt)
        return C

    def total(self, C: list) -> int:
        return sum(len(C[t]) for t in self.targets.tolist())

    def price(self, v: int) -> int:
        return len(self.base[v])


# ------------------------------------------------------------------ contest

def cost(m, S) -> int:
    state = m.name(m.base, S) if len(S) else m.base
    return sum(m.price(v) for v in S) + m.total(state)


def greedy(m, cands: list[int], k: int, log) -> tuple[list[int], list[int]]:
    """Greedy library of size k. Returns (picks, cost after each pick)."""
    state, picks, costs = m.base, [], []
    current = m.total(state)
    for step in range(k):
        best, best_cost, best_state = None, None, None
        for v in cands:
            if v in picks:
                continue
            s = m.name(state, [v])
            c = m.total(s) + m.price(v)
            if best_cost is None or c < best_cost:
                best, best_cost, best_state = v, c, s
        if best_cost >= current:          # nothing helps any more
            break
        picks.append(best)
        state, current = best_state, best_cost
        costs.append(current + sum(m.price(v) for v in picks[:-1]))
        log(f"    pick {step + 1}: id {best}, cost {costs[-1]}")
    return picks, costs


def gains(m, cands: list[int]) -> dict[int, int]:
    """Naming gain of each candidate on its own (saving minus price)."""
    base = m.total(m.base)
    return {v: base - m.total(m.name(m.base, [v])) - m.price(v) for v in cands}


def matched_random(H: list[int], cands: list[int], L: np.ndarray, size: np.ndarray, named: set[int],
                   rng, draws: int) -> list[list[int]]:
    """Random libraries matching H theorem for theorem (same proof length, nearest size)."""
    pools = []
    for h in H:
        for tol in (0, 2, 4, 8):
            pool = [v for v in cands if v not in named and L[v] == L[h] and abs(size[v] - size[h]) <= tol]
            if len(pool) >= 5:
                break
        pools.append(pool)
    out = []
    for _ in range(draws):
        S = set()
        for pool in pools:
            free = [v for v in pool if v not in S]
            S.add(int(rng.choice(free)))
        out.append(sorted(S))
    return out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run", type=Path)
    ap.add_argument("--slack", type=int, default=4)
    ap.add_argument("--draws", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr, flush=True)
    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    g = Hypergraph.load(args.run)
    with open(args.run / "theorems.csv", newline="") as f:
        th = list(csv.DictReader(f))
    with open(args.run / "scores.csv", newline="") as f:
        sc = list(csv.DictReader(f))
    targets = np.array([r["is_target"] == "1" for r in sc])
    is_cand = np.array([r["is_candidate"] == "1" for r in sc])
    size = np.array([int(r["size"]) for r in th])
    named_mask = np.array([bool(r["pm"] or r["setmm"]) for r in th])
    cands = [int(v) for v in np.flatnonzero(is_cand & (g.L0 > 1))]
    named = {v for v in cands if named_mask[v]}
    H = sorted(named)
    H_pm = sorted(v for v in H if th[v]["pm"])
    k = len(H)
    log(f"{int(targets.sum())} library theorems, {len(cands)} candidates, {k} named ({len(H_pm)} with a Principia number)")

    measures = {"tree": TreeCost(g, targets)}
    t1 = time.time()
    universe = g.L0 <= g.N - args.slack
    measures["dag"] = DagCost(g, targets, universe)
    log(f"DAG sizes computed in {time.time() - t1:.0f}s ({measures['dag'].unreached} theorems unreached)")

    report: dict = {"run": str(args.run), "k": k, "n_library": int(targets.sum()), "n_candidates": len(cands),
                    "human": [th[v]["readable"] for v in H], "human_pm": [th[v]["readable"] for v in H_pm]}
    solo: dict[str, dict[int, int]] = {}
    for name, m in measures.items():
        log(f"\n[{name}] baseline cost {m.total(m.base)}")
        t1 = time.time()
        solo[name] = gains(m, cands)
        log(f"  naming gain for {len(cands)} candidates in {time.time() - t1:.0f}s")
        base = m.total(m.base)
        save = lambda S: base - cost(m, S)
        picks, _ = greedy(m, cands, k, log)
        topk = sorted(cands, key=lambda v: -solo[name][v])[:k]
        rand = matched_random(H, cands, g.L0, size, named, rng, args.draws)
        rand_s = np.array([save(S) for S in rand])
        rand_pm = np.array([save(S[:len(H_pm)]) for S in matched_random(H_pm, cands, g.L0, size, named, rng, args.draws)])
        greedy_pm, _ = (picks[:len(H_pm)], None)
        res = {
            "baseline": base,
            "greedy": {"saving": save(picks), "picks": [th[v]["readable"] for v in picks],
                       "named_picked": [th[v]["readable"] for v in picks if v in named]},
            "top_k": {"saving": save(topk), "picks": [th[v]["readable"] for v in topk]},
            "human": {"saving": save(H)},
            "human_pm": {"saving": save(H_pm), "greedy_same_size": save(greedy_pm)},
            "random": {"mean": float(rand_s.mean()), "p95": float(np.quantile(rand_s, 0.95)), "max": int(rand_s.max()),
                       "human_percentile": float((rand_s < save(H)).mean() + 0.5 * (rand_s == save(H)).mean())},
            "random_pm": {"mean": float(rand_pm.mean()), "p95": float(np.quantile(rand_pm, 0.95)),
                          "human_percentile": float((rand_pm < save(H_pm)).mean() + 0.5 * (rand_pm == save(H_pm)).mean())},
            # Where the human lemmas rank by naming gain under this measure.
            "human_gain_ranks": {th[v]["readable"]: 1 + sum(1 for u in cands if solo[name][u] > solo[name][v]) for v in H},
        }
        report[name] = res
        log(f"  greedy {res['greedy']['saving']}, top-k {res['top_k']['saving']}, human {res['human']['saving']}, "
            f"random mean {res['random']['mean']:.0f} (human beats {100 * res['random']['human_percentile']:.0f}%)")

    # Question 2: does naming gain still pick out the human names under DAG size?
    rows = []
    for v in cands:
        rows.append({"named": v in named, "min_steps": float(g.L0[v]), "size": float(size[v]),
                     "gain_tree": float(solo["tree"][v]), "gain_dag": float(solo["dag"][v])})
    auc = {}
    for col in ("gain_tree", "gain_dag"):
        r = evaluate(rows, col, 1, np.random.default_rng(args.seed))
        auc[col] = {"auc": r["auc"], "matched": r.get("matched"), "n_matched": r.get("n_matched")}
    report["auc"] = auc
    from scipy.stats import spearmanr
    report["spearman_tree_vs_dag"] = float(spearmanr([x["gain_tree"] for x in rows], [x["gain_dag"] for x in rows])[0])

    out = args.run / "lemma_contest.json"
    out.write_text(json.dumps(report, indent=1, ensure_ascii=False))
    (args.run / "lemma_contest.md").write_text(markdown(report))
    print(markdown(report))
    log(f"\nwritten to {out} and lemma_contest.md ({time.time() - t0:.0f}s)")


def markdown(r: dict) -> str:
    out = [f"# Lemma contest: {r['run']}\n",
           f"Library: {r['n_library']} theorems. Candidates: {r['n_candidates']}. "
           f"Human set: the {r['k']} named candidates (Principia-only subset: {len(r['human_pm'])}).\n",
           "Saving = total proof length of the library without named lemmas, minus the cost with them "
           "(each named lemma paid for once). Higher is better.\n",
           "| measure | baseline cost | greedy | top-k by gain | human | random (mean / 95th pct) | human beats random | human as % of greedy |",
           "|---|---|---|---|---|---|---|---|"]
    for m in ("tree", "dag"):
        x = r[m]
        out.append(f"| {m} | {x['baseline']} | {x['greedy']['saving']} | {x['top_k']['saving']} | {x['human']['saving']} | "
                   f"{x['random']['mean']:.0f} / {x['random']['p95']:.0f} | {100 * x['random']['human_percentile']:.0f}% | "
                   f"{100 * x['human']['saving'] / x['greedy']['saving']:.0f}% |")
    out.append("\nPrincipia-only human set (same contest, smaller k):\n")
    out.append("| measure | greedy (same k) | Principia set | random mean / 95th pct | Principia beats random |")
    out.append("|---|---|---|---|---|")
    for m in ("tree", "dag"):
        x = r[m]
        out.append(f"| {m} | {x['human_pm']['greedy_same_size']} | {x['human_pm']['saving']} | "
                   f"{x['random_pm']['mean']:.0f} / {x['random_pm']['p95']:.0f} | {100 * x['random_pm']['human_percentile']:.0f}% |")
    for m in ("tree", "dag"):
        out.append(f"\n## Greedy picks ({m})\n")
        named = set(r[m]["greedy"]["named_picked"])
        for i, p in enumerate(r[m]["greedy"]["picks"], 1):
            out.append(f"{i}. `{p}`" + (" (human-named)" if p in named else ""))
    out.append("\n## Does naming gain pick out the human names under each measure?\n")
    out.append("| naming gain under | AUC | matched AUC (same size and proof length) |")
    out.append("|---|---|---|")
    for col, label in (("gain_tree", "tree size"), ("gain_dag", "DAG size")):
        a = r["auc"][col]
        m = f"{fmt(a['matched'])}, {a['n_matched']} named" if a["matched"] else "n/a"
        out.append(f"| {label} | {fmt(a['auc'])} | {m} |")
    out.append(f"\nSpearman correlation between the two gains over all candidates: {r['spearman_tree_vs_dag']:.3f}.\n")
    out.append("## Rank of each human lemma by naming gain\n")
    out.append("| lemma | tree rank | DAG rank |")
    out.append("|---|---|---|")
    for p in r["human"]:
        out.append(f"| `{p}` | {r['tree']['human_gain_ranks'][p]} | {r['dag']['human_gain_ranks'][p]} |")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    main()
