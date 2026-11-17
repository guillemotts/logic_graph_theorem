"""Do the scores pick out the theorems humans named?

Positives are generated theorems that carry a human name: a Principia
Mathematica number (pmproofs.txt) or a set.mm label. Axioms and redundant
theorems are excluded.

For each score this reports:

  AUC          Probability that a named theorem outranks an unnamed one
               (0.5 = chance), with a bootstrap 95% interval over the named
               theorems. There are only a dozen or so, so intervals are wide.
  matched AUC  The same, but each named theorem is compared only with unnamed
               theorems of the same statement size and the same proof length.
               This is the null model: a score has to beat what size and
               length alone predict.
  stability    With --compare, the Spearman rank correlation of the score
               between two horizons, over the candidates they share.

If `supernode_scores.csv` exists (logicgraph.supernodes), the same report is
repeated per supernode level: a supernode counts as named when any member is
named, size is its representative's size, and supernode size (number of
members) is added as a baseline.

Usage:
    python -m logicgraph.validate data/gen/luk21 --compare data/gen/luk19
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

# (column, label, sign): sign -1 means "smaller is expected to be more named".
CANDIDATE_SCORES = [
    ("gain", "naming gain", 1), ("knockout", "knockout", 1), ("lost", "lost if removed", 1),
    ("affected", "affected if removed", 1),
]
BASELINES = [
    ("size", "small statement", -1), ("min_steps", "short proof", -1), ("n_uses", "times used as premise", 1),
    ("min_uses", "used in shortest proofs", 1), ("n_derivations", "times re-derived", 1),
]
DEEP = ("deep", "deep (steps / size)", 1)
NO_MATCH = {"size", "min_steps", "deep"}      # functions of the matching variables


def load(run: Path) -> list[dict]:
    with open(run / "theorems.csv", newline="") as f:
        theorems = {int(r["id"]): r for r in csv.DictReader(f)}
    rows = []
    with open(run / "scores.csv", newline="") as f:
        for s in csv.DictReader(f):
            if s["is_target"] != "1" or s["min_steps"] == "1":
                continue
            t = theorems[int(s["id"])]
            row = {"id": int(s["id"]), "formula": t["formula"], "readable": t["readable"],
                   "pm": t["pm"], "setmm": t["setmm"], "candidate": s["is_candidate"] == "1"}
            for k in ("min_steps", "size", "n_uses", "min_uses", "n_derivations"):
                row[k] = float(s[k])
            row["deep"] = float(s["deep"])
            for k, _, _ in CANDIDATE_SCORES:
                row[k] = float(s[k]) if s[k] != "" else None
            row["named"] = bool(t["pm"] or t["setmm"])
            rows.append(row)
    return rows


def wins(x: float, others: np.ndarray) -> float:
    """Fraction of `others` that x beats, counting ties as half."""
    return float(((others < x).sum() + 0.5 * (others == x).sum()) / len(others))


def interval(w: list[float], rng: np.random.Generator, reps: int = 4000) -> tuple[float, float, float]:
    a = np.array(w)
    boot = a[rng.integers(0, len(a), size=(reps, len(a)))].mean(axis=1)
    return float(a.mean()), float(np.quantile(boot, 0.025)), float(np.quantile(boot, 0.975))


def evaluate(rows: list[dict], col: str, sign: int, rng) -> dict:
    pos = [r for r in rows if r["named"]]
    neg = np.array([sign * r[col] for r in rows if not r["named"]])
    plain = [wins(sign * r[col], neg) for r in pos]
    out = {"n_pos": len(pos), "auc": interval(plain, rng)}
    if col in NO_MATCH:
        return out
    matched, n_controls = [], []
    for r in pos:
        for tol in (0, 2, 4):          # exact size first, then widen a little if nothing matches
            ctrl = np.array([sign * q[col] for q in rows if not q["named"]
                             and q["min_steps"] == r["min_steps"] and abs(q["size"] - r["size"]) <= tol])
            if len(ctrl) >= 5:
                break
        if len(ctrl):
            matched.append(wins(sign * r[col], ctrl))
            n_controls.append(len(ctrl))
    if matched:
        out["matched"] = interval(matched, rng)
        out["n_matched"] = len(matched)
        out["median_controls"] = int(np.median(n_controls))
    return out


def fmt(triple) -> str:
    m, lo, hi = triple
    return f"{m:.2f} ({lo:.2f}–{hi:.2f})"


SUPER_SCORES = CANDIDATE_SCORES + [("n_members", "supernode size (baseline)", 1),
                                   ("size", "small statement (baseline)", -1),
                                   ("min_steps", "short proof (baseline)", -1)]


def load_supernodes(run: Path) -> dict[int, list[dict]]:
    by_level: dict[int, list[dict]] = {}
    with open(run / "supernode_scores.csv", newline="") as f:
        for r in csv.DictReader(f):
            if r["is_candidate"] != "1" or r["min_steps"] == "1":
                continue
            row = {"formula": r["formula"], "readable": r["readable"], "names": r["names"],
                   "named": int(r["n_named"]) > 0, "n_members": float(r["n_members"]),
                   "min_steps": float(r["min_steps"]), "size": float(r["rep_size"])}
            for k, _, _ in CANDIDATE_SCORES:
                row[k] = float(r[k])
            by_level.setdefault(int(r["level"]), []).append(row)
    return by_level


def supernode_report(args, rng, say) -> None:
    from .supernodes import LEVEL_NAMES
    levels = load_supernodes(args.run)
    say("\n# Supernodes\n")
    say("Near-duplicate theorems collapsed into supernodes (see `logicgraph/supernodes.py`). Gain and "
        "knockout make free or forbid every member at once; the library is the set of supernodes.\n")
    say("| level | candidate supernodes | named | score | AUC | matched AUC (same size and proof length) |")
    say("|---|---|---|---|---|---|")
    for k, rows in sorted(levels.items()):
        for col, label, sign in SUPER_SCORES:
            res = evaluate(rows, col, sign, rng)
            m = (f"{fmt(res['matched'])}, {res['n_matched']} named" if "matched" in res else "n/a")
            say(f"| {k} ({LEVEL_NAMES[k]}) | {len(rows)} | {res['n_pos']} | {label} | {fmt(res['auc'])} | {m} |")

    top = max(levels)
    rows = levels[top]
    say(f"\n## Named supernodes at level {top}\n")
    say("| representative | members | names | steps | gain rank | knockout rank |")
    say("|---|---|---|---|---|---|")
    rank = lambda col, r: 1 + sum(1 for q in rows if q[col] > r[col])
    for r in sorted((r for r in rows if r["named"]), key=lambda r: rank("gain", r)):
        say(f"| `{r['readable']}` | {int(r['n_members'])} | {r['names']} | {int(r['min_steps'])} | "
            f"{rank('gain', r)} / {len(rows)} | {rank('knockout', r)} / {len(rows)} |")
    for col, label in (("gain", "naming gain"), ("knockout", "knockout")):
        say(f"\n## Top {args.top} unnamed supernodes at level {top} by {label}\n")
        say(f"| # | representative | members | steps | {label} |")
        say("|---|---|---|---|---|")
        shown = 0
        for i, r in enumerate(sorted(rows, key=lambda r: -r[col]), start=1):
            if r["named"]:
                continue
            say(f"| {i} | `{r['readable']}` | {int(r['n_members'])} | {int(r['min_steps'])} | {int(r[col])} |")
            shown += 1
            if shown == args.top:
                break

    if args.compare and (args.compare / "supernode_scores.csv").exists():
        other = load_supernodes(args.compare)
        say(f"\n## Supernode stability across horizons ({args.compare.name} vs {args.run.name})\n")
        say("Supernodes are matched by their representative.\n")
        say("| level | score | shared supernodes | Spearman |")
        say("|---|---|---|---|")
        for k in sorted(levels):
            mine = {r["formula"]: r for r in levels[k]}
            theirs = {r["formula"]: r for r in other.get(k, [])}
            shared = sorted(mine.keys() & theirs.keys())
            for col, label, _ in CANDIDATE_SCORES[:2]:
                rho = spearmanr([mine[f][col] for f in shared], [theirs[f][col] for f in shared])[0]
                say(f"| {k} | {label} | {len(shared)} | {rho:.3f} |")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run", type=Path)
    ap.add_argument("--compare", type=Path, help="a run at another horizon, for rank stability")
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args(argv)
    rng = np.random.default_rng(args.seed)
    rows = load(args.run)
    cands = [r for r in rows if r["candidate"]]
    out: list[str] = []
    say = out.append

    say(f"# Validation: {args.run}\n")
    say(f"- Library (targets): {len(rows)} non-redundant theorems, {sum(r['named'] for r in rows)} named.")
    say(f"- Candidates for gain/knockout: {len(cands)}, {sum(r['named'] for r in cands)} named.")
    say("- AUC = chance a named theorem outranks an unnamed one; 0.5 is chance. Brackets are bootstrap 95% intervals.\n")

    say("## Scores vs human names\n")
    say("| score | evaluated on | named | AUC | matched AUC (same size and proof length) |")
    say("|---|---|---|---|---|")
    results = {}
    plan = [(c, l, s, "candidates", cands) for c, l, s in CANDIDATE_SCORES]
    plan += [(*DEEP, "library", rows)]
    plan += [(c, l + " (baseline)", s, "candidates", cands) for c, l, s in BASELINES]
    for col, label, sign, where, data in plan:
        res = results[col] = evaluate(data, col, sign, rng)
        m = (f"{fmt(res['matched'])}, {res['n_matched']} named, median {res['median_controls']} controls"
             if "matched" in res else "n/a (it is a function of size and length)")
        say(f"| {label} | {where} | {res['n_pos']} | {fmt(res['auc'])} | {m} |")

    say("\n## Where each named theorem ranks\n")
    say("Rank 1 is the highest score. Gain and knockout ranks are among the candidates; deep is among the library.\n")
    say("| theorem | names | steps | size | gain rank | knockout rank | deep rank |")
    say("|---|---|---|---|---|---|---|")

    def rank(data, col, r):
        if r[col] is None:
            return "–"
        return f"{1 + sum(1 for q in data if q[col] > r[col])} / {len(data)}"

    for r in sorted((r for r in rows if r["named"]), key=lambda r: (r["min_steps"], r["size"])):
        names = "; ".join(x for x in (r["pm"], r["setmm"]) if x)
        g = rank(cands, "gain", r) if r["candidate"] else "–"
        k = rank(cands, "knockout", r) if r["candidate"] else "–"
        say(f"| `{r['readable']}` | {names} | {int(r['min_steps'])} | {int(r['size'])} | {g} | {k} | {rank(rows, 'deep', r)} |")

    for col, label, data in [("gain", "naming gain", cands), ("knockout", "knockout", cands), ("deep", "deep", rows)]:
        say(f"\n## Top {args.top} unnamed by {label}\n")
        say(f"| # | theorem | steps | size | {label} |")
        say("|---|---|---|---|---|")
        ranked = sorted(data, key=lambda r: -r[col])
        shown = 0
        for i, r in enumerate(ranked, start=1):
            if r["named"]:
                continue
            value = f"{r[col]:.2f}" if col == "deep" else f"{int(r[col])}"
            say(f"| {i} | `{r['readable']}` | {int(r['min_steps'])} | {int(r['size'])} | {value} |")
            shown += 1
            if shown == args.top:
                break

    if args.compare:
        other = {r["formula"]: r for r in load(args.compare)}
        say(f"\n## Stability across horizons ({args.compare.name} vs {args.run.name})\n")
        say("Spearman rank correlation over the theorems scored in both runs; top-20 overlap counts shared entries.\n")
        say("| score | shared theorems | Spearman | top-20 overlap |")
        say("|---|---|---|---|")
        for col, label, _ in CANDIDATE_SCORES:      # deep does not depend on the horizon
            pairs = [(r[col], other[r["formula"]][col]) for r in rows
                     if r["formula"] in other and r[col] is not None and other[r["formula"]][col] is not None]
            a, b = zip(*pairs)
            shared = [r["formula"] for r in rows if r["formula"] in other and r[col] is not None
                      and other[r["formula"]][col] is not None]
            top_a = set(sorted(shared, key=lambda f: -next(r[col] for r in rows if r["formula"] == f))[:20]) \
                if len(shared) < 5000 else set()
            top_b = set(sorted(shared, key=lambda f: -other[f][col])[:20])
            overlap = f"{len(top_a & top_b)} / 20" if top_a else "–"
            say(f"| {label} | {len(pairs)} | {spearmanr(a, b)[0]:.3f} | {overlap} |")

    if (args.run / "supernode_scores.csv").exists():
        supernode_report(args, rng, say)

    text = "\n".join(out) + "\n"
    (args.run / "validation.md").write_text(text)
    print(text)
    print(f"written to {args.run / 'validation.md'}", file=sys.stderr)


if __name__ == "__main__":
    main()
