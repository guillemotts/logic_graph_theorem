"""The map of logics: which principles follow from which, with certificates.

Every logic here is minimal logic (ax-1, ax-2, reductio) plus some principles
from `principles.CATALOG`. For each base logic B and principle P the map
records one of:

  given      P is one of B's axioms.
  refuted    A countermodel: a truth table where all of B holds, modus ponens
             preserves truth, and P fails. Certain: B never proves P.
  proved     An explicit condensed-detachment proof of P from B's axioms,
             found by exhaustive search up to the horizon.
  chained    B proves every axiom of another base B', and B' proves P, so B
             proves P (derivability is transitive). Lists the route.
  instance   B's base logic (minimal, intuitionistic or classical) proves
             "I1 -> (I2 -> P)" for substitution instances I1, I2 of B's extra
             principles, checked exactly by the decision procedure; so B proves
             P by modus ponens. The instances are listed.
  decided    No proof found inside the horizon, but an exact decision procedure
             shows P is a theorem of a logic B is known to contain: minimal
             logic always, intuitionistic logic when B proves explosion,
             classical logic (truth tables) when B proves ax-3.
  unknown    Neither a proof nor a countermodel was found.

Bases: minimal logic, minimal + each non-minimal principle, and intuitionistic
logic (minimal + explosion) + each principle that is not intuitionistic. Bases
that prove each other's principles are the same logic and become one node; a
node sits below another when the higher one proves everything the lower one
assumes, and the edge is certified strict by a countermodel.

The generated library (logicgraph.generate, Łukasiewicz axioms, i.e. classical
logic) is tagged theorem by theorem with the weakest of minimal /
intuitionistic / classical that proves it (exact), and each node gets bounds on
how much of the library it proves.

Usage:
    python -m logicgraph.logicmap data/logics --library data/gen/luk21 [--horizon 17 --deep-horizon 19]
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

from .formula import canon, parse_polish, to_polish, to_str, variables
from .generate import generate
from .intuitionistic import is_theorem
from .matrices import Matrix, all_models, evaluate_batch, failing_assignment, validity_table
from .principles import BASE, CATALOG, NAMED_LOGICS
from .subsumption import GeneralizationIndex

LADDER = ("minimal", "intuitionistic", "classical")


def base_list() -> list[tuple[str, ...]]:
    nonminimal = [p.key for p in CATALOG if not is_theorem(p.formula, "minimal")]
    nonintuitionistic = [k for k in nonminimal if k != "EFQ" and not is_theorem(next(
        p for p in CATALOG if p.key == k).formula, "intuitionistic")]
    bases = [()] + [(k,) for k in nonminimal] + [("EFQ", k) for k in nonintuitionistic]
    return bases


def describe(base: tuple[str, ...]) -> str:
    return NAMED_LOGICS.get(base) or ("intuitionistic + " + " + ".join(base[1:]) if base[:1] == ("EFQ",) and len(base) > 1
                                      else "minimal + " + " + ".join(base))


class MapBuilder:
    def __init__(self, log):
        self.log = log
        self.principles = CATALOG
        self.keys = [p.key for p in CATALOG]
        self.formula = {p.key: p.formula for p in BASE + CATALOG}
        t0 = time.time()
        self.models = all_models()
        cols = [p.key for p in BASE] + self.keys
        table = validity_table([self.formula[k] for k in cols], self.models)
        self.valid = {k: table[:, j] for j, k in enumerate(cols)}
        self.base_ok = self.valid["K"] & self.valid["S"] & self.valid["RED"]
        self.log(f"{len(self.models)} candidate models, {int(self.base_ok.sum())} are models of minimal logic "
                 f"[{time.time() - t0:.1f}s]")

    def countermodel(self, base: tuple[str, ...], target: str) -> int | None:
        ok = self.base_ok.copy()
        for k in base:
            ok &= self.valid[k]
        hits = np.flatnonzero(ok & ~self.valid[target])
        if not len(hits):
            return None
        # Prefer the smallest model, then Heyting algebras (listed first).
        return int(min(hits.tolist(), key=lambda i: (self.models[i].n, i)))

    def refute_base(self, base: tuple[str, ...]) -> dict[str, dict]:
        """Cells for one base: given, refuted (with a countermodel), or still open ("unknown")."""
        cells: dict[str, dict] = {}
        for k in self.keys:
            if k in base:
                cells[k] = {"status": "given"}
                continue
            m = self.countermodel(base, k)
            cells[k] = ({"status": "refuted", "model": m,
                         "falsified_by": failing_assignment(self.formula[k], self.models[m])}
                        if m is not None else {"status": "unknown"})
        return cells

    def search(self, base: tuple[str, ...], targets: list[str], horizon: int, cache: Path | None) -> tuple[dict, int]:
        """Look for proofs of `targets` from the base's axioms, up to `horizon` steps.

        Returns ({target: proved cell}, number of theorems generated). Results are
        cached per (base, horizon, targets) because a single search can take minutes.
        """
        name = ("+".join(base) or "minimal") + f"_h{horizon}_" + "+".join(sorted(targets))
        path = cache / f"{name}.json" if cache else None
        if path and path.exists():
            saved = json.loads(path.read_text())
            self.log(f"  {describe(base):40s} {horizon} steps: cached, proved {sorted(saved['found'])}")
            return saved["found"], saved["n_theorems"]
        axiom_keys = [p.key for p in BASE] + list(base)
        axs = [self.formula[k] for k in axiom_keys]
        hits: dict[str, int] = {}
        index = GeneralizationIndex()

        def on_level(u, n, new):
            for i in new:
                index.add(i, u.formulas[i])
            for k in targets:
                if k not in hits:
                    for i, _ in index.generalizations(self.formula[k]):
                        hits[k] = i
                        break
            return all(k in hits for k in targets)

        t0 = time.time()
        u = generate(axs, horizon, on_level=on_level)
        found = {k: {"status": "proved", "steps": u.steps[i], "proof": u.proof[i],
                     "proves": to_str(u.formulas[i]), "axioms": axiom_keys} for k, i in hits.items()}
        self.log(f"  {describe(base):40s} searched to {u.max_steps} steps "
                 f"({len(u)} theorems, {time.time() - t0:.0f}s): proved {sorted(found)}")
        if path:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"found": found, "n_theorems": len(u)}))
        return found, len(u)


def proves(cells: dict, key: str) -> bool:
    return cells.get(key, {}).get("status") in ("given", "proved", "chained", "instance", "decided")


def rung_of(cells: dict) -> str:
    """The strongest of minimal / intuitionistic / classical that a base is known to contain."""
    return "classical" if proves(cells, "AX3") else "intuitionistic" if proves(cells, "EFQ") else "minimal"


def _substitute(t, sub: dict):
    if isinstance(t, int):
        return sub[t]
    return tuple(_substitute(x, sub) for x in t)


def _pool(target) -> list:
    """Small formulas over the target's variables, to substitute into a principle."""
    vs = sorted(variables(target))
    pool = list(vs) + [(v,) for v in vs] + [((v,),) for v in vs]
    pool += [(a, b) for a in vs for b in vs] + [(a, (b,)) for a in vs for b in vs] + [((a,), b) for a in vs for b in vs]
    return pool


def instances(t, pool: list) -> list:
    k = sorted(variables(t))
    return [_substitute(t, dict(zip(k, choice))) for choice in itertools.product(pool, repeat=len(k))]


def derive_by_instances(bases, cells, formulas: dict) -> int:
    """Settle open cells by showing the base logic proves (instances of extras) -> target."""
    settled = 0
    for b in bases:
        c = cells[b]
        rung = rung_of(c)
        extras = [k for k in b if not (rung != "minimal" and k == "EFQ")]
        for k, cell in c.items():
            if cell["status"] != "unknown" or not extras:
                continue
            target = formulas[k]
            pool = _pool(target)
            insts = [(e, i) for e in extras for i in instances(formulas[e], pool)]
            hit = next(([x] for x in insts if is_theorem((x[1], target), rung)), None)
            if hit is None:
                hit = next(([x, y] for x, y in itertools.combinations(insts, 2)
                            if is_theorem((x[1], (y[1], target)), rung)), None)
            if hit:
                c[k] = {"status": "instance", "by": rung,
                        "instances": [{"of": e, "formula": to_str(i)} for e, i in hit]}
                settled += 1
    return settled


def chain(bases, cells, keys) -> int:
    """Close derivability under transitivity; returns the number of cells upgraded.

    If B proves all of B2's axioms, everything B2 proves, B proves too. A
    chained result that hits a countermodel would mean a bug, so it raises.
    """
    upgraded = 0
    changed = True
    while changed:
        changed = False
        for b in bases:
            for b2 in bases:
                if b2 == b or not all(proves(cells[b], k) for k in b2):
                    continue
                for k in keys:
                    if proves(cells[b2], k) and not proves(cells[b], k):
                        if cells[b][k]["status"] == "refuted":
                            raise AssertionError(f"{b} proves {b2} which proves {k}, but {k} is refuted over {b}")
                        cells[b][k] = {"status": "chained", "via": list(b2),
                                       "previously": cells[b][k]["status"]}
                        upgraded += 1
                        changed = True
    return upgraded


def decide(bases, cells, formulas: dict) -> int:
    """Settle open cells with the exact decision procedures; returns the number settled.

    A base that proves ax-3 contains Łukasiewicz's complete classical system, so
    it proves every tautology. One that proves explosion contains intuitionistic
    logic; every base contains minimal logic. (Each step relies on the
    completeness of the corresponding Hilbert system, a standard result.)
    """
    settled = 0
    for b in bases:
        c = cells[b]
        rung = rung_of(c)
        for k, cell in c.items():
            if cell["status"] == "unknown" and is_theorem(formulas[k], rung):
                c[k] = {"status": "decided", "by": rung}
                settled += 1
    return settled


def close(bases, cells, formulas, log) -> None:
    """Alternate chaining, deciding and instance derivations until nothing changes."""
    total = {"chained": 0, "decided": 0, "instance": 0}
    while True:
        step = {"chained": chain(bases, cells, list(formulas)), "decided": decide(bases, cells, formulas)}
        if not any(step.values()):
            step["instance"] = derive_by_instances(bases, cells, formulas)
        for k, v in step.items():
            total[k] += v
        if not any(step.values()):
            break
    log("closure: " + ", ".join(f"{v} {k}" for k, v in total.items()))


def build_nodes(bases, cells, keys):
    """Group bases into logics and compute the strict order between them."""
    extras = {b: set(b) for b in bases}
    closure = {b: {k for k in keys if proves(cells[b], k)} for b in bases}
    # Same logic: each proves the other's axioms.
    groups: list[list[tuple]] = []
    for b in bases:
        for g in groups:
            a = g[0]
            if extras[a] <= closure[b] and extras[b] <= closure[a]:
                g.append(b)
                break
        else:
            groups.append([b])
    nodes = []
    for g in groups:
        rep = min(g, key=lambda b: (len(b), b))
        nodes.append({"bases": g, "rep": rep, "proves": sorted(closure[rep]),
                      "refutes": sorted(k for k in keys if cells[rep][k]["status"] == "refuted"),
                      "unknown": sorted(k for k in keys if cells[rep][k]["status"] == "unknown")})
    # a <= b when b proves everything a assumes.
    n = len(nodes)
    le = [[extras[nodes[i]["rep"]] <= closure[nodes[j]["rep"]] for j in range(n)] for i in range(n)]
    edges = []
    for i in range(n):
        for j in range(n):
            if i == j or not le[i][j] or le[j][i]:
                continue
            if any(k != i and k != j and le[i][k] and le[k][j] and not le[k][i] and not le[j][k] for k in range(n)):
                continue        # not a covering edge
            # Certificate that j is strictly stronger: a principle of j refuted over i.
            lo, hi = nodes[i]["rep"], nodes[j]["rep"]
            witness = next((k for k in sorted(extras[hi] | closure[hi])
                            if cells[lo][k]["status"] == "refuted"), None)
            edges.append({"from": i, "to": j, "adds": sorted(extras[hi] - closure[lo]),
                          "strict_by": witness, "model": cells[lo][witness]["model"] if witness else None})
    return nodes, edges


def tag_library(run: Path, log) -> list[dict]:
    with open(run / "scores.csv", newline="") as f:
        sc = {int(r["id"]): r for r in csv.DictReader(f)}
    with open(run / "theorems.csv", newline="") as f:
        rows = [r for r in csv.DictReader(f)
                if sc[int(r["id"])]["is_target"] == "1" or sc[int(r["id"])]["subsumed_by"] != ""]
    t0 = time.time()
    for r in rows:
        t = parse_polish(r["formula"])
        r["logic"] = next(l for l in LADDER if is_theorem(t, l))
        r["redundant"] = sc[int(r["id"])]["subsumed_by"] != ""
    log(f"tagged {len(rows)} library theorems by logic [{time.time() - t0:.0f}s]")
    return rows


def library_bounds(nodes, builder: MapBuilder, library: list[dict], log, per_profile: int = 8):
    """Per node: library theorems it surely proves (lower) and at most proves (upper).

    Upper bounds and breakage use small models of minimal logic (at most 4
    values): up to `per_profile` of the smallest for each distinct pattern of
    which catalog principles hold.
    """
    lib = [r for r in library if not r["redundant"]]
    formulas = [canon(parse_polish(r["formula"])) for r in lib]
    by_profile: dict[tuple, list[int]] = {}
    for i in sorted(np.flatnonzero(builder.base_ok).tolist(), key=lambda i: (builder.models[i].n, i)):
        if builder.models[i].n > 4:
            continue
        key = tuple(bool(builder.valid[k][i]) for k in builder.keys)
        if len(by_profile.setdefault(key, [])) < per_profile:
            by_profile[key].append(i)
    reps = sorted(i for g in by_profile.values() for i in g)
    t0 = time.time()
    fails = ~validity_table(formulas, [builder.models[i] for i in reps])
    log(f"evaluated {len(formulas)} library theorems in {len(reps)} small models "
        f"({len(by_profile)} validity patterns) [{time.time() - t0:.0f}s]")
    logic = np.array([r["logic"] for r in lib])
    for node in nodes:
        assumed = set(node["rep"]) | set(node["proves"])
        rung = ("classical" if "DNE" in node["proves"] else
                "intuitionistic" if "EFQ" in node["proves"] else "minimal")
        lower = int(np.isin(logic, LADDER[:LADDER.index(rung) + 1]).sum())
        models_here = [r for r, i in enumerate(reps) if all(builder.valid[k][i] for k in assumed)]
        upper = int((~fails[models_here].any(axis=0)).sum()) if models_here else len(lib)
        node["library"] = {"lower": lower, "upper": upper, "total": len(lib)}
    return reps, fails, lib


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out", type=Path, help="output directory, e.g. data/logics")
    ap.add_argument("--library", type=Path, help="a generated run to tag, e.g. data/gen/luk21")
    ap.add_argument("--horizon", type=int, default=17)
    ap.add_argument("--deep-horizon", type=int, default=19, help="second pass for bases with open questions")
    ap.add_argument("--max-theorems", type=int, default=250_000,
                    help="skip the second pass for bases whose first pass generated more theorems than this")
    ap.add_argument("--viz", type=Path, default=Path("viz/logic_map.js"))
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr)
    t0 = time.time()
    b = MapBuilder(log)
    bases = base_list()
    log(f"{len(bases)} base logics, {len(b.keys)} principles, horizon {args.horizon}")
    cache = args.out / "cache"
    formulas = {k: b.formula[k] for k in b.keys}
    cells = {base: b.refute_base(base) for base in bases}
    sizes = {}
    for base in bases:
        open_targets = [k for k, c in cells[base].items() if c["status"] == "unknown"]
        if open_targets:
            found, sizes[base] = b.search(base, open_targets, args.horizon, cache)
            cells[base].update(found)
    close(bases, cells, formulas, log)
    # Second, deeper pass for bases that still have open questions (skipping explosive ones).
    for base in bases:
        open_targets = [k for k, c in cells[base].items() if c["status"] == "unknown"]
        if open_targets and sizes.get(base, 0) <= args.max_theorems:
            found, _ = b.search(base, open_targets, args.deep_horizon, cache)
            cells[base].update(found)
    close(bases, cells, formulas, log)
    nodes, edges = build_nodes(bases, cells, b.keys)

    library, breakage, library_models = None, {}, []
    if args.library:
        library = tag_library(args.library, log)
        reps, fails, lib = library_bounds(nodes, b, library, log)
        # For the browser sandbox: the small models and which library theorems fail in each,
        # so new principles can be bounded without re-evaluating the library.
        import base64
        for r, i in enumerate(reps):
            bits = np.packbits(fails[r].astype(np.uint8))           # big-endian within each byte
            library_models.append({**b.models[i].to_dict(), "fails": base64.b64encode(bits.tobytes()).decode()})
        # Breakage: among small models of minimal logic where P is false, the one where the
        # fewest library theorems fail ("the least you lose if P is false").
        counts = fails.sum(axis=1)
        for k in b.keys:
            where = [r for r, i in enumerate(reps) if not b.valid[k][i]]
            if not where:
                breakage[k] = {"models": 0, "broken": None, "total": len(lib)}
                continue
            best = min(where, key=lambda r: (counts[r], b.models[reps[r]].n))
            model = reps[best]
            keep = [kk for kk in b.keys if b.valid[kk][model]]
            breakage[k] = {"models": len(where), "broken": int(counts[best]), "total": len(lib),
                           "model": model, "still_true": keep}

    used_models = sorted({c["model"] for base in bases for c in cells[base].values() if "model" in c}
                         | {v["model"] for v in breakage.values() if v.get("model") is not None})
    out = {
        "horizon": args.horizon, "deep_horizon": args.deep_horizon,
        "principles": [{"key": p.key, "name": p.name, "formula": to_str(p.formula), "polish": p.polish,
                        "note": p.note, "weakest": next(l for l in LADDER if is_theorem(p.formula, l))}
                       for p in CATALOG],
        "base_axioms": [{"key": p.key, "name": p.name, "formula": to_str(p.formula)} for p in BASE],
        "bases": [{"axioms": list(base), "name": describe(base), "cells": cells[base]} for base in bases],
        "nodes": [{**n, "bases": [list(x) for x in n["bases"]], "rep": list(n["rep"]),
                   "names": [describe(x) for x in n["bases"]]} for n in nodes],
        "edges": edges,
        "models": {str(i): b.models[i].to_dict() for i in used_models},
        "breakage": breakage,
        "library_models": library_models,
    }
    if library is not None:
        counts = {l: sum(1 for r in library if not r["redundant"] and r["logic"] == l) for l in LADDER}
        out["library"] = {"source": str(args.library), "by_logic": counts,
                          "total": sum(counts.values())}
        with open(args.library / "logic_tags.csv", "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["id", "logic"])
            for r in library:
                w.writerow([r["id"], r["logic"]])
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "logic_map.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    args.viz.parent.mkdir(parents=True, exist_ok=True)
    args.viz.write_text("window.LOGIC_MAP = " + json.dumps(out, ensure_ascii=False, separators=(",", ":")) + ";\n")

    status = {}
    for base in bases:
        for c in cells[base].values():
            status[c["status"]] = status.get(c["status"], 0) + 1
    log(f"\ncells: {status}")
    log(f"{len(nodes)} distinct logics, {len(edges)} covering edges")
    for i, n in enumerate(nodes):
        lib_txt = f"  library {n['library']['lower']}-{n['library']['upper']} of {n['library']['total']}" if "library" in n else ""
        log(f"  [{i}] {' = '.join(describe(x) for x in n['bases'])}{lib_txt}")
    for e in edges:
        log(f"  [{e['from']}] -> [{e['to']}]  strict by {e['strict_by']}")
    log(f"-> {args.out / 'logic_map.json'}, {args.viz} ({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()
