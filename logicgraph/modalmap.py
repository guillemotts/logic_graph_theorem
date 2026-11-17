"""The map of modal logics: which modal principles follow from which, with certificates.

Every logic is K (classical logic, the K axiom, necessitation) plus some of the
principles below. For each base logic B and principle P:

  given      P is one of B's axioms.
  refuted    A Kripke frame (up to 4 worlds) on which all of B's axioms are valid
             but P is not. Certain: B never proves P.
  instance   K proves "these instances of B's axioms, also under □ and □□, imply
             P" (exact K tableau), so B proves P by necessitation and modus ponens.
  decided    K proves P outright; or B contains S4 (resp. S5) and P is an S4
             (resp. S5) theorem by the exact decision procedure.
  chained    B proves every axiom of another base B', which proves P.
  unknown    None of the above.

Bases: all 32 combinations of D, T, B, 4, 5 (the "modal cube"), plus .2, S4.2
and Löb's axiom. Bases that prove each other's axioms are one logic.

The bridge: the Gödel–McKinsey–Tarski translation sends intuitionistic logic
into S4 and classical logic into S5. It is checked here on a sample of the
generated library: intuitionistic tags must match S4 validity of the
translation exactly, and every classical theorem's translation must be S5-valid.

Usage:
    python -m logicgraph.modalmap data/logics --library data/gen/luk21
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import random
import signal
import sys
import time
from pathlib import Path

import numpy as np

from . import formula as F
from .logicmap import build_nodes, chain, proves
from .modal import (box, conj, depth, dia, failing_point, frame_dict, frame_validity, frames, godel_translation,
                    imp, is_valid, neg, parse_polish, s5_valid_small, substitute, to_str, variables)

PRINCIPLES = [
    ("D", "D (seriality)", "CLpMp", "what is necessary is possible"),
    ("T", "T (reflexivity)", "CLpp", "what is necessary is true"),
    ("B", "B (symmetry)", "CpLMp", "what is true is necessarily possible"),
    ("4", "4 (transitivity)", "CLpLLp", "what is necessary is necessarily necessary"),
    ("5", "5 (euclidean)", "CMpLMp", "what is possible is necessarily possible"),
    ("G", ".2 (confluence)", "CMLpLMp", "if possibly necessary, then necessarily possible"),
    ("L", "Löb (provability)", "CLCLppLp", "□ read as 'provable': Löb's theorem"),
]
CUBE = ["D", "T", "B", "4", "5"]
SPECIAL = {(): "K", ("T", "4"): "S4", ("T", "5"): "S5", ("T", "B"): "KTB", ("T", "4", "G"): "S4.2",
           ("L",): "GL", ("G",): "K.2", ("D",): "KD", ("T",): "KT"}


def describe(base: tuple) -> str:
    return SPECIAL.get(tuple(base)) or "K" + "".join(base)


def bases() -> list[tuple]:
    out = [tuple(c) for r in range(len(CUBE) + 1) for c in itertools.combinations(CUBE, r)]
    return out + [("G",), ("T", "4", "G"), ("L",)]


def instance_pool(target) -> list:
    """Small modal formulas over the target's variables, to substitute into principles."""
    pool = []
    for v in sorted(variables(target)):
        lits = [v, neg(v)]
        pool += lits
        for a in lits:
            pool += [box(a), dia(a), box(box(a)), dia(dia(a)), box(dia(a)), dia(box(a)), conj(a, box(a)),
                     imp(box(a), a), imp(a, box(a))]
    seen, out = set(), []
    for x in pool:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def boxed(t, d: int):
    """t ∧ □t ∧ ... ∧ □^d t."""
    out, cur = t, t
    for _ in range(d):
        cur = box(cur)
        out = conj(out, cur)
    return out


class ModalMapBuilder:
    def __init__(self, max_worlds: int, log):
        self.log = log
        self.keys = [k for k, *_ in PRINCIPLES]
        self.formula = {k: parse_polish(p) for k, _, p, _ in PRINCIPLES}
        t0 = time.time()
        self.frames = frames(max_worlds)
        self.valid = frame_validity([self.formula[k] for k in self.keys], self.frames)
        log(f"{len(self.frames)} frames with up to {max_worlds} worlds [{time.time() - t0:.1f}s]")

    def refute(self, base: tuple) -> dict:
        cells = {}
        ok = np.ones(len(self.frames), dtype=bool)
        for k in base:
            ok &= self.valid[:, self.keys.index(k)]
        for j, k in enumerate(self.keys):
            if k in base:
                cells[k] = {"status": "given"}
                continue
            hits = np.flatnonzero(ok & ~self.valid[:, j])
            if len(hits):
                i = int(min(hits.tolist(), key=lambda i: (self.frames[i].shape[0], self.frames[i].sum(), i)))
                cells[k] = {"status": "refuted", "model": i, "falsified_by": failing_point(self.formula[k], self.frames[i])}
            else:
                cells[k] = {"status": "unknown"}
        return cells

    def by_instances(self, base: tuple, target_key: str) -> dict | None:
        """Look for instances of the base's axioms (under up to d boxes) that make K prove the target."""
        target = self.formula[target_key]
        d = depth(target) + 1
        pool = instance_pool(target)
        insts = []
        for e in base:
            ax = self.formula[e]
            for choice in itertools.product(pool, repeat=len(variables(ax))):
                insts.append((e, substitute(ax, dict(zip(sorted(variables(ax)), choice)))))
        for size in (1, 2, 3):
            if size == 3 and len(insts) > 60:
                break
            for combo in itertools.combinations(insts, size):
                premise = boxed(combo[0][1], d)
                for _, i in combo[1:]:
                    premise = conj(premise, boxed(i, d))
                if is_valid(imp(premise, target), "K"):
                    return {"status": "instance", "by": "K", "depth": d,
                            "instances": [{"of": e, "formula": to_str(i)} for e, i in combo]}
        return None

    def decide(self, all_bases, cells) -> int:
        settled = 0
        for b in all_bases:
            c = cells[b]
            rung = ("S5" if proves(c, "T") and proves(c, "5") else
                    "S4" if proves(c, "T") and proves(c, "4") else "K")
            for k in self.keys:
                if c[k]["status"] != "unknown":
                    continue
                t = self.formula[k]
                ok = is_valid(t, "K") or (rung == "S4" and is_valid(t, "S4")) or \
                    (rung == "S5" and (is_valid(t, "S4") or s5_valid_small(t)))
                if ok:
                    c[k] = {"status": "decided", "by": rung}
                    settled += 1
        return settled


def check_bridge(library: Path, per_logic: int, seconds: int, log) -> dict:
    """Gödel–McKinsey–Tarski on a stratified sample of the generated library."""
    with open(library / "scores.csv", newline="") as f:
        redundant = {int(r["id"]) for r in csv.DictReader(f) if r["subsumed_by"] != ""}
    with open(library / "logic_tags.csv", newline="") as f:
        tags = {int(r["id"]): r["logic"] for r in csv.DictReader(f) if int(r["id"]) not in redundant}
    with open(library / "theorems.csv", newline="") as f:
        formula = {int(r["id"]): r["formula"] for r in csv.DictReader(f) if int(r["id"]) in tags}
    rng = random.Random(0)
    sample = []
    for logic in ("minimal", "intuitionistic", "classical"):
        ids = sorted(i for i, l in tags.items() if l == logic)
        sample += rng.sample(ids, min(per_logic, len(ids)))

    class Timeout(Exception):
        pass

    def alarm(*_):
        raise Timeout()

    old = signal.signal(signal.SIGALRM, alarm)
    rows = {"s4_agree": 0, "s4_disagree": 0, "s4_timeout": 0, "s5_ok": 0, "s5_fail": 0, "s5_skipped": 0}
    disagreements = []
    t0 = time.time()
    try:
        for i in sample:
            t = F.parse_polish(formula[i])
            g = godel_translation(t)
            expect = tags[i] in ("minimal", "intuitionistic")
            signal.alarm(seconds)
            try:
                got = is_valid(g, "S4")
                signal.alarm(0)
                if got == expect:
                    rows["s4_agree"] += 1
                else:
                    rows["s4_disagree"] += 1
                    disagreements.append(F.to_str(t))
            except Timeout:
                rows["s4_timeout"] += 1
            finally:
                signal.alarm(0)
            if len(F.variables(t)) <= 4:
                rows["s5_ok" if s5_valid_small(g) else "s5_fail"] += 1
            else:
                rows["s5_skipped"] += 1
    finally:
        signal.signal(signal.SIGALRM, old)
    log(f"bridge: {len(sample)} library theorems [{time.time() - t0:.0f}s]: {rows}")
    # Showcase: classical principles whose translations are S5 but not S4 theorems.
    show = []
    for name, polish in [("double-negation elimination", "CNNpp"), ("Peirce's law", "CCCpqpp"),
                         ("explosion", "CNpCpq"), ("ax-1", "CpCqp")]:
        t = F.canon(F.parse_polish(polish))
        g = godel_translation(t)
        show.append({"name": name, "formula": F.to_str(t), "translation": to_str(g),
                     "S4": is_valid(g, "S4"), "S5": s5_valid_small(g)})
    return {"sample": len(sample), "per_logic": per_logic, "timeout_seconds": seconds, **rows,
            "disagreements": disagreements[:10], "examples": show}


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out", type=Path, help="output directory, e.g. data/logics")
    ap.add_argument("--library", type=Path, help="generated run with logic_tags.csv, for the bridge check")
    ap.add_argument("--max-worlds", type=int, default=4)
    ap.add_argument("--bridge-sample", type=int, default=300, help="library theorems per logic tag")
    ap.add_argument("--bridge-seconds", type=int, default=10, help="time limit per S4 check")
    ap.add_argument("--viz", type=Path, default=Path("viz/modal_map.js"))
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr)
    t0 = time.time()
    b = ModalMapBuilder(args.max_worlds, log)
    all_bases = bases()
    cells = {base: b.refute(base) for base in all_bases}
    n_open = sum(c["status"] == "unknown" for base in all_bases for c in cells[base].values())
    log(f"{len(all_bases)} bases x {len(b.keys)} principles: {n_open} cells open after countermodel search")

    # Close under: K/S4/S5 decisions, chaining, and instance derivations (in that order of cost).
    while True:
        changed = b.decide(all_bases, cells) + chain(all_bases, cells, b.keys)
        if changed:
            continue
        for base in sorted(all_bases, key=len):
            for k in b.keys:
                if cells[base][k]["status"] == "unknown":
                    hit = b.by_instances(base, k)
                    if hit:
                        cells[base][k] = hit
                        changed += 1
                        break                    # let chaining spread it before searching more
            if changed:
                break
        if not changed:
            break
    status = {}
    for base in all_bases:
        for c in cells[base].values():
            status[c["status"]] = status.get(c["status"], 0) + 1
    log(f"cells: {status} [{time.time() - t0:.0f}s]")

    nodes, edges = build_nodes(all_bases, cells, b.keys)
    bridge = check_bridge(args.library, args.bridge_sample, args.bridge_seconds, log) if args.library else None
    used = sorted({c["model"] for base in all_bases for c in cells[base].values() if "model" in c})
    out = {
        "kind": "modal",
        "principles": [{"key": k, "name": n, "formula": to_str(parse_polish(p)), "polish": p, "note": note,
                        "weakest": "K" if is_valid(parse_polish(p), "K") else
                                   "S4" if is_valid(parse_polish(p), "S4") else "beyond S4"}
                       for k, n, p, note in PRINCIPLES],
        "bases": [{"axioms": list(base), "name": describe(base), "cells": cells[base]} for base in all_bases],
        "nodes": [{**n, "bases": [list(x) for x in n["bases"]], "rep": list(n["rep"]),
                   "names": [describe(x) for x in n["bases"]]} for n in nodes],
        "edges": edges,
        "models": {str(i): frame_dict(b.frames[i]) for i in used},
        "bridge": bridge,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "modal_map.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    args.viz.write_text("window.MODAL_MAP = " + json.dumps(out, ensure_ascii=False, separators=(",", ":")) + ";\n")
    log(f"{len(nodes)} distinct logics, {len(edges)} covering edges")
    for i, n in enumerate(nodes):
        log(f"  [{i}] {' = '.join(describe(x) for x in n['bases'])}   unknown: {n['unknown']}")
    for e in edges:
        log(f"  [{e['from']}] -> [{e['to']}]  adds {e['adds']}  strict by {e['strict_by']}")
    log(f"-> {args.out / 'modal_map.json'}, {args.viz} ({time.time() - t0:.0f}s)")


if __name__ == "__main__":
    main()
