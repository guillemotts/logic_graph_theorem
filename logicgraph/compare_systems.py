"""Is a lemma's importance a property of the lemma, or of the axiom system?

Takes two generated runs from different axiom systems (logicgraph.generate,
then logicgraph.hyperscores on each) and compares them on the theorems both
reach:

  - proof length: how well L in one system predicts L in the other;
  - each score: Spearman rank correlation over the shared candidates, and the
    overlap of the top 20 / top 100;
  - human names: AUC of each score in each system, on the shared candidates
    only, so the two systems are judged on the same theorems;
  - the theorems that rank high in both, and the ones that rank high in one
    system only.

This works for systems that reach many of the same theorems (two horizons of
one system, or systems sharing axioms). Lukasiewicz's two systems share only 80
theorems within 21 steps; for those, use logicgraph.transfer.

Usage:
    python -m logicgraph.compare_systems data/gen/luk21 data/gen/clav21
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

from .validate import evaluate, fmt, load

SCORES = [("gain", "naming gain"), ("knockout", "knockout"), ("affected", "affected if removed")]


def ranks(values: np.ndarray) -> np.ndarray:
    """Rank 1 = highest value; ties share the best rank."""
    order = np.sort(-values)
    return np.searchsorted(order, -values, side="left") + 1


def compare(a_run: Path, b_run: Path, rng) -> tuple[dict, list[str]]:
    A = {r["formula"]: r for r in load(a_run)}
    B = {r["formula"]: r for r in load(b_run)}
    meta = [json.loads((run / "meta.json").read_text()) for run in (a_run, b_run)]
    na, nb = a_run.name, b_run.name
    out: list[str] = []
    say = out.append
    res: dict = {"a": na, "b": nb, "axioms": [m["axioms"] for m in meta]}

    lib = sorted(A.keys() & B.keys())
    shared = [f for f in lib if A[f]["candidate"] and B[f]["candidate"]]
    named_lib = [f for f in lib if A[f]["named"]]
    res.update(n_lib=[len(A), len(B)], n_shared_lib=len(lib), n_shared_cands=len(shared),
               n_named_shared=len(named_lib), n_named_shared_cands=sum(A[f]["named"] for f in shared))

    say(f"# Two axiom systems: {na} vs {nb}\n")
    say(f"- {na}: axioms `{meta[0]['axioms']}`, horizon {meta[0]['max_steps']} steps.")
    say(f"- {nb}: axioms `{meta[1]['axioms']}`, horizon {meta[1]['max_steps']} steps.")
    say(f"- Library (non-redundant targets): {len(A)} vs {len(B)}; in both: {len(lib)} "
        f"({len(named_lib)} named).")
    say(f"- Candidates in both: {len(shared)} ({res['n_named_shared_cands']} named).\n")

    if len(shared) < 20:
        say("Too few shared candidates to compare rankings: the two systems reach almost entirely "
            "different theorems within the horizon. See logicgraph.transfer for a comparison that "
            "doesn't need shared theorems.")
        return res, out

    la = np.array([A[f]["min_steps"] for f in lib])
    lb = np.array([B[f]["min_steps"] for f in lib])
    rho_L = spearmanr(la, lb)[0]
    res["spearman_steps"] = rho_L
    say("## Proof length\n")
    say(f"Spearman correlation of shortest proof length over the {len(lib)} shared theorems: {rho_L:.3f}.\n")

    say("## Do the systems agree on which lemmas matter?\n")
    say("Over the candidates in both libraries. Top-k overlap counts shared entries; "
        "random sets would share about k²/n.\n")
    say("| score | Spearman | top-20 overlap | top-100 overlap |")
    say("|---|---|---|---|")
    res["scores"] = {}
    for col, label in SCORES:
        xa = np.array([A[f][col] for f in shared])
        xb = np.array([B[f][col] for f in shared])
        rho = spearmanr(xa, xb)[0]
        oa, ob = np.argsort(-xa, kind="stable"), np.argsort(-xb, kind="stable")   # ties broken by formula
        top = {k: len(set(oa[:k]) & set(ob[:k])) for k in (20, 100)}
        res["scores"][col] = {"spearman": rho, "top20": top[20], "top100": top[100]}
        say(f"| {label} | {rho:.3f} | {top[20]} / 20 | {top[100]} / 100 |")
    # partial out proof length: correlation of gain after ranking within each pair of lengths
    xa = np.array([A[f]["gain"] for f in shared]); xb = np.array([B[f]["gain"] for f in shared])
    resid = []
    for d in (A, B):
        x = np.array([d[f]["gain"] for f in shared], dtype=float)
        L = np.array([d[f]["min_steps"] for f in shared])
        r = np.empty_like(x)
        for v in np.unique(L):
            m = L == v
            r[m] = (ranks(x[m]) - 0.5) / m.sum()     # percentile within its own proof length
        resid.append(r)
    rho_within = spearmanr(*resid)[0]
    res["spearman_gain_within_length"] = rho_within
    say(f"\nNaming gain grows with proof length in both systems. Ranked within each proof length "
        f"(percentile among candidates of the same length, in each system), the correlation is {rho_within:.3f}.\n")

    say("## Human names, judged on the same theorems in each system\n")
    say("AUC of named vs unnamed over the shared candidates; matched AUC compares each named theorem "
        "with unnamed ones of the same size and proof length *in that system*.\n")
    say(f"| score | AUC in {na} | AUC in {nb} | matched AUC in {na} | matched AUC in {nb} |")
    say("|---|---|---|---|---|")
    res["auc"] = {}
    for col, label in SCORES:
        ev = [evaluate([d[f] for f in shared], col, 1, rng) for d in (A, B)]
        res["auc"][col] = [{"auc": e["auc"], "matched": e.get("matched")} for e in ev]
        m = [fmt(e["matched"]) if e.get("matched") else "–" for e in ev]
        say(f"| {label} | {fmt(ev[0]['auc'])} | {fmt(ev[1]['auc'])} | {m[0]} | {m[1]} |")

    say("\n## Named lemmas in both systems\n")
    say(f"Gain rank among the {len(shared)} shared candidates (1 = highest). Steps = shortest proof.\n")
    say(f"| lemma | names | steps {na} | steps {nb} | gain rank {na} | gain rank {nb} |")
    say("|---|---|---|---|---|---|")
    ga = ranks(np.array([A[f]["gain"] for f in shared])); gb = ranks(np.array([B[f]["gain"] for f in shared]))
    pos = {f: i for i, f in enumerate(shared)}
    res["named"] = []
    for f in sorted(named_lib, key=lambda f: (A[f]["min_steps"], A[f]["size"])):
        names = "; ".join(x for x in (A[f]["pm"], A[f]["setmm"]) if x)
        i = pos.get(f)
        r_a, r_b = (int(ga[i]), int(gb[i])) if i is not None else (None, None)
        res["named"].append({"formula": f, "names": names, "steps": [A[f]["min_steps"], B[f]["min_steps"]],
                             "gain_rank": [r_a, r_b]})
        say(f"| `{A[f]['readable']}` | {names} | {int(A[f]['min_steps'])} | {int(B[f]['min_steps'])} | "
            f"{r_a or '–'} | {r_b or '–'} |")

    def table(title, fs):
        say(f"\n## {title}\n")
        say(f"| theorem | named | steps {na} / {nb} | gain rank {na} | gain rank {nb} |")
        say("|---|---|---|---|---|")
        for f in fs:
            i = pos[f]
            say(f"| `{A[f]['readable']}` | {'yes' if A[f]['named'] else ''} | "
                f"{int(A[f]['min_steps'])} / {int(B[f]['min_steps'])} | {int(ga[i])} | {int(gb[i])} |")

    worst = np.maximum(ga, gb)
    both = [shared[i] for i in np.argsort(worst, kind="stable")[:15]]
    res["top_both"] = [{"formula": f, "rank": [int(ga[pos[f]]), int(gb[pos[f]])]} for f in both]
    table("High in both (sorted by the worse of the two ranks)", both)
    only_a = [shared[i] for i in np.argsort(ga, kind="stable") if gb[i] > len(shared) // 4][:8]
    only_b = [shared[i] for i in np.argsort(gb, kind="stable") if ga[i] > len(shared) // 4][:8]
    table(f"High in {na} only (bottom three quarters in {nb})", only_a)
    table(f"High in {nb} only (bottom three quarters in {na})", only_b)
    return res, out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("a", type=Path)
    ap.add_argument("b", type=Path)
    ap.add_argument("--out", type=Path, help="markdown report (default: <b>/compare_<a>.md)")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args(argv)
    res, out = compare(args.a, args.b, np.random.default_rng(args.seed))
    text = "\n".join(out) + "\n"
    path = args.out or args.b / f"compare_{args.a.name}.md"
    path.write_text(text)
    path.with_suffix(".json").write_text(json.dumps(res, indent=1, default=float) + "\n")
    print(text)
    print(f"written to {path}", file=sys.stderr)


if __name__ == "__main__":
    main()
