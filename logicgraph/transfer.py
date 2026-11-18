"""Does a lemma that is useful in one axiom system help in another?

The 21-step neighbourhoods of two axiom systems hardly overlap (Lukasiewicz's
ax-1..3 and his syllogism / Clavius / Duns Scotus system share 80 of 228k and
401k theorems), so the two can't be compared on common theorems. Instead each
lemma is *transferred*: added as an extra axiom (cost 1 step) to a system, and
the system's own library is regenerated.

  saving_X(v) = sum over X's library t (t != v) of L_X(t) - L_{X+v}(t)

Exactness: the library is the theorems with L_X(t) <= B. A shorter proof of t
has fewer than L_X(t) steps, so regenerating X + v up to B steps finds every
improvement; the saving is exact (unlike naming gain on a fixed hypergraph,
which is a lower bound). This works for lemmas that X itself cannot reach.

Lemmas come from each system's candidates (21-step runs): its named lemmas,
its top lemmas by naming gain, and a random sample. Each lemma is scored in
both systems ("home" and "away").

Usage:
    python -m logicgraph.transfer data/gen/luk19 data/gen/clav19 \
        --pools data/gen/luk21 data/gen/clav21 --out data/gen/transfer
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

from .formula import axioms as load_axioms, canon, parse_polish, to_polish
from .generate import generate
from .validate import evaluate, fmt


def library(run: Path) -> tuple[str, dict[str, int], int]:
    """(axiom spec, {polish: L} for the run's non-redundant targets, bound on L)."""
    meta = json.loads((run / "meta.json").read_text())
    lib = {}
    with open(run / "theorems.csv", newline="") as f:
        formulas = [r["formula"] for r in csv.DictReader(f)]
    with open(run / "scores.csv", newline="") as f:
        for s in csv.DictReader(f):
            if s["is_target"] == "1":
                lib[formulas[int(s["id"])]] = int(s["min_steps"])
    return meta["axioms"], lib, max(lib.values())


def saving(spec: str, lib: dict[str, int], bound: int, extra: str) -> tuple[int, int]:
    """(total saving, number of library theorems that get shorter) when `extra` is added as an axiom."""
    axs = load_axioms(spec)
    v = canon(parse_polish(extra))
    if v in axs:
        return 0, 0
    u = generate(axs + [v], bound)
    new = {to_polish(t): s for t, s in zip(u.formulas, u.steps)}
    total = improved = 0
    for f, L in lib.items():
        if f == extra:
            continue
        d = L - new[f]          # every library theorem is still provable, never longer
        assert d >= 0, f
        total += d
        improved += d > 0
    return total, improved


_LIBS: dict = {}


def _init(runs: list[str]) -> None:
    for r in runs:
        _LIBS[r] = library(Path(r))


def _job(args: tuple[str, str]) -> tuple[str, str, int, int, float]:
    run, extra = args
    spec, lib, bound = _LIBS[run]
    t = time.time()
    s, n = saving(spec, lib, bound, extra)
    return run, extra, s, n, time.time() - t


def pool(run: Path, n_top: int, n_random: int, rng) -> list[dict]:
    """Lemmas from a run's candidates: all named, top n_top by naming gain, n_random at random."""
    with open(run / "theorems.csv", newline="") as f:
        th = list(csv.DictReader(f))
    cands = []
    with open(run / "scores.csv", newline="") as f:
        for s in csv.DictReader(f):
            if s["is_candidate"] == "1" and s["min_steps"] != "1":
                t = th[int(s["id"])]
                cands.append({"formula": t["formula"], "readable": t["readable"], "named": bool(t["pm"] or t["setmm"]),
                              "names": "; ".join(x for x in (t["pm"], t["setmm"]) if x),
                              "size": int(t["size"]), "home_steps": int(s["min_steps"]), "home_gain": int(s["gain"])})
    by_gain = sorted(cands, key=lambda c: -c["home_gain"])
    rank = {c["formula"]: i + 1 for i, c in enumerate(by_gain)}
    picked: dict[str, dict] = {}
    for c in cands:
        if c["named"]:
            picked[c["formula"]] = dict(c, why="named")
    for c in by_gain[:n_top]:
        picked.setdefault(c["formula"], dict(c, why="top"))
    unnamed = [c for c in cands if not c["named"]]
    for i in rng.choice(len(unnamed), size=min(n_random, len(unnamed)), replace=False):
        c = unnamed[int(i)]
        if c["formula"] in picked:
            picked[c["formula"]]["random"] = True
        else:
            picked[c["formula"]] = dict(c, why="random", random=True)
    for c in picked.values():
        c["home_gain_rank"] = rank[c["formula"]]
        c["n_candidates"] = len(cands)
        c.setdefault("random", False)
    return list(picked.values())


def partial_spearman(x, y, z) -> float:
    """Spearman correlation of x and y after removing the rank-linear effect of z from each."""
    from scipy.stats import rankdata
    rx, ry, rz = (rankdata(a) for a in (x, y, z))
    res = lambda r: r - np.polyval(np.polyfit(rz, r, 1), rz)
    return float(np.corrcoef(res(rx), res(ry))[0, 1])


def analyse(lemmas: list[dict], names: list[str], rng) -> tuple[dict, list[str]]:
    out: list[str] = []
    say = out.append
    res: dict = {}
    for home, away in (names, names[::-1]):
        L = [c for c in lemmas if c["home"] == home]
        R = [c for c in L if c["random"]]
        sh = np.array([c["saving"][home] for c in R]); sa = np.array([c["saving"][away] for c in R])
        sz = np.array([c["size"] for c in R])
        r = {"n": len(L), "n_random": len(R),
             "spearman": float(spearmanr(sh, sa)[0]),
             "partial_size": partial_spearman(sh, sa, sz),
             "spearman_size_away": float(spearmanr(-sz, sa)[0]),
             "zero_away": float((sa == 0).mean())}
        # Top lemmas at home: where do they land among random ones away?
        top = [c for c in L if c["why"] == "top"]
        pct = lambda x: float((sa < x).mean() + 0.5 * (sa == x).mean())
        r["top_away_percentile"] = float(np.median([pct(c["saving"][away]) for c in top])) if top else None
        r["top_home_percentile"] = float(np.median([float((sh < c["saving"][home]).mean() + 0.5 * (sh == c["saving"][home]).mean()) for c in top])) if top else None
        # Named lemmas vs random ones, away, matched on size and home proof length.
        rows = [{"named": c["why"] == "named", "min_steps": float(c["home_steps"]), "size": float(c["size"]),
                 "home": float(c["saving"][home]), "away": float(c["saving"][away])}
                for c in L if c["why"] == "named" or (c["random"] and not c["named"])]
        n_named = sum(x["named"] for x in rows)
        if n_named >= 3:
            r["named"] = {col: evaluate(rows, col, 1, rng) for col in ("home", "away")}
            r["n_named"] = n_named
        res[home] = r

    say("## Does usefulness transfer?\n")
    say("Each lemma's saving at home and away, over the randomly sampled lemmas of each system "
        "(so the sample isn't biased toward good ones). Partial correlation removes the effect of statement size.\n")
    say("| lemmas from | sampled | Spearman home vs away | partial (size removed) | "
        "small statement vs away saving | no saving away | top-50 at home: median percentile away |")
    say("|---|---|---|---|---|---|---|")
    for home, away in (names, names[::-1]):
        r = res[home]
        say(f"| {home} (away = {away}) | {r['n_random']} | {r['spearman']:.2f} | {r['partial_size']:.2f} | "
            f"{r['spearman_size_away']:.2f} | {100 * r['zero_away']:.0f}% | "
            f"{100 * r['top_away_percentile']:.0f}% (at home: {100 * r['top_home_percentile']:.0f}%) |")

    for home, away in (names, names[::-1]):
        r = res[home]
        if "named" not in r:
            continue
        say(f"\n## Named lemmas from {home}, tried in {away}\n")
        say(f"{r['n_named']} named lemmas vs the random unnamed ones. Matched AUC compares each named lemma "
            f"with unnamed ones of the same size and the same proof length in {home}.\n")
        say("| saving measured in | AUC | matched AUC |")
        say("|---|---|---|")
        for col, label in (("home", home), ("away", away)):
            e = r["named"][col]
            say(f"| {label} | {fmt(e['auc'])} | {fmt(e['matched']) if e.get('matched') else '–'} |")
        L = sorted((c for c in lemmas if c["home"] == home and c["why"] == "named"),
                   key=lambda c: -c["saving"][away])
        R = np.array([c["saving"][away] for c in lemmas if c["home"] == home and c["random"]])
        say(f"\n| lemma | names | saving in {home} | saving in {away} | percentile among random, in {away} |")
        say("|---|---|---|---|---|")
        for c in L:
            p = (R < c["saving"][away]).mean() + 0.5 * (R == c["saving"][away]).mean()
            say(f"| `{c['readable']}` | {c['names']} | {c['saving'][home]} | {c['saving'][away]} | {100 * p:.0f}% |")

    say("\n## The most useful lemmas in each system, and how they do in the other\n")
    for home, away in (names, names[::-1]):
        L = [c for c in lemmas if c["home"] == home]
        R = np.array([c["saving"][away] for c in L if c["random"]])
        say(f"\n### From {home}\n")
        say(f"| lemma | named | saving in {home} | saving in {away} | percentile among random, in {away} |")
        say("|---|---|---|---|---|")
        for c in sorted(L, key=lambda c: -c["saving"][home])[:12]:
            p = (R < c["saving"][away]).mean() + 0.5 * (R == c["saving"][away]).mean()
            say(f"| `{c['readable']}` | {'yes' if c['named'] else ''} | {c['saving'][home]} | {c['saving'][away]} | {100 * p:.0f}% |")
    return res, out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("libraries", type=Path, nargs=2, help="two runs whose libraries the savings are measured on")
    ap.add_argument("--pools", type=Path, nargs=2, required=True, help="runs to draw lemmas from (same order)")
    ap.add_argument("--top", type=int, default=50)
    ap.add_argument("--random", type=int, default=300)
    ap.add_argument("--workers", type=int, default=9)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=Path, default=Path("data/gen/transfer"))
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr, flush=True)
    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    names = [p.name.rstrip("0123456789") for p in args.pools]
    libs = [str(p) for p in args.libraries]
    lemmas = []
    for name, p in zip(names, args.pools):
        for c in pool(p, args.top, args.random, rng):
            c["home"] = name
            c["saving"], c["improved"] = {}, {}
            lemmas.append(c)
    log(f"{len(lemmas)} lemmas; libraries: " +
        ", ".join(f"{n} {len(library(Path(l))[1])} theorems (L <= {library(Path(l))[2]})" for n, l in zip(names, libs)))

    by_key = {}
    jobs = []
    for i, c in enumerate(lemmas):
        for lib in libs:
            jobs.append((lib, c["formula"]))
            by_key.setdefault((lib, c["formula"]), []).append(i)
    lib_name = dict(zip(libs, names))
    slow = []
    with Pool(args.workers, initializer=_init, initargs=(libs,)) as P:
        for k, (lib, f, s, n, dt) in enumerate(P.imap_unordered(_job, sorted(set(jobs)), chunksize=1), start=1):
            for i in by_key[(lib, f)]:
                lemmas[i]["saving"][lib_name[lib]] = s
                lemmas[i]["improved"][lib_name[lib]] = n
            slow.append(dt)
            if k % 50 == 0:
                log(f"  {k}/{len(set(jobs))} ({time.time() - t0:.0f}s)")

    res, out = analyse(lemmas, names, np.random.default_rng(args.seed))
    head = [f"# Lemma transfer: {names[0]} ↔ {names[1]}\n",
            f"A lemma is added as an extra axiom to a system and that system's library is regenerated "
            f"(exact savings). Libraries: " + ", ".join(
                f"{n} = `{library(Path(l))[0]}`, {len(library(Path(l))[1])} theorems with L ≤ {library(Path(l))[2]}"
                for n, l in zip(names, libs)) + ".",
            f"Lemmas: from each system, its named candidates, its top {args.top} by naming gain and "
            f"{args.random} sampled at random ({len(lemmas)} in all).\n"]
    text = "\n".join(head + out) + "\n"
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "transfer.md").write_text(text)
    (args.out / "transfer.json").write_text(json.dumps({"summary": res, "lemmas": lemmas}, indent=1,
                                                       ensure_ascii=False, default=float) + "\n")
    print(text)
    log(f"written to {args.out}/transfer.md ({time.time() - t0:.0f}s; slowest lemma {max(slow):.0f}s)")


if __name__ == "__main__":
    main()
