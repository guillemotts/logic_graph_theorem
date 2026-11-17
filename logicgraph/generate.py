"""Exhaustively generate every theorem provable in at most N condensed-detachment steps.

"Steps" is the length of the D-proof string (tree size): an axiom is 1 step and
`D a b` is 1 + steps(a) + steps(b), so lengths are always odd.

Enumeration goes by length. A theorem whose shortest proof has n steps is
`D a b` for theorems a, b whose shortest proofs have i and j steps with
i + j = n - 1, so trying every such pair finds every theorem, with no
dependence on search order.

Every successful detachment is recorded as a derivation, including the ones
that re-derive an already known theorem. The result is an AND-OR hypergraph:

    theorems.csv     one row per theorem (node)
    derivations.csv  one row per (major, minor) -> conclusion (hyperedge)

Horizon rule: the derivations recorded are exactly those with
steps(major) + steps(minor) + 1 <= N.

Usage:
    python -m logicgraph.generate data/gen/luk21 --max-steps 21 [--axioms lukasiewicz]
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

from .formula import axioms as load_axioms, cd, size, to_polish, to_str, variables


@dataclass
class Universe:
    max_steps: int
    formulas: list = field(default_factory=list)          # id -> canonical formula
    steps: list[int] = field(default_factory=list)        # id -> shortest proof length
    proof: list[str] = field(default_factory=list)        # id -> one shortest D-proof
    derivations: list[tuple[int, int, int]] = field(default_factory=list)   # (conclusion, major, minor)
    n_axioms: int = 0

    def __len__(self) -> int:
        return len(self.formulas)


def generate(axs: list, max_steps: int, log=None, on_level=None) -> Universe:
    """Generate every theorem with a proof of at most max_steps steps.

    `on_level(universe, n, new_ids)` is called after each proof length n; if it
    returns True, generation stops there (and `max_steps` is set to n).
    """
    u = Universe(max_steps)
    ids: dict = {}
    levels: dict[int, list[int]] = {1: []}
    for k, a in enumerate(axs):
        if a in ids:
            raise ValueError(f"axiom {k + 1} duplicates an earlier axiom")
        ids[a] = len(u.formulas)
        u.formulas.append(a); u.steps.append(1); u.proof.append(str(k + 1))
        levels[1].append(ids[a])
    u.n_axioms = len(axs)
    t0 = time.time()
    for n in range(3, max_steps + 1, 2):
        new: list[int] = []
        for i in range(1, n - 1, 2):
            minors = levels[n - 1 - i]
            for a in levels[i]:
                fa = u.formulas[a]
                if isinstance(fa, int) or len(fa) != 2:
                    continue            # only an implication can be a major premise
                for b in minors:
                    c = cd(fa, u.formulas[b])
                    if c is None:
                        continue
                    cid = ids.get(c)
                    if cid is None:
                        cid = ids[c] = len(u.formulas)
                        u.formulas.append(c); u.steps.append(n)
                        u.proof.append("D" + u.proof[a] + u.proof[b])
                        new.append(cid)
                    u.derivations.append((cid, a, b))
        levels[n] = new
        if log:
            log(f"  {n:3d} steps: {len(new):8d} new, {len(u):8d} theorems, "
                f"{len(u.derivations):9d} derivations ({time.time() - t0:.1f}s)")
        if on_level is not None and on_level(u, n, new):
            u.max_steps = n
            break
    return u


def load_names(pm_csv: Path | None, setmm_nodes: Path | None) -> tuple[dict, dict]:
    """Human names for formulas: Principia numbers and set.mm labels, keyed by Polish form."""
    from .formula import canon, parse_infix
    pm: dict[str, list[str]] = {}
    if pm_csv and pm_csv.exists():
        with open(pm_csv, newline="") as f:
            for r in csv.DictReader(f):
                pm.setdefault(r["formula"], []).append((r["number"] + " " + r["name"]).strip())
    setmm: dict[str, list[str]] = {}
    if setmm_nodes and setmm_nodes.exists():
        with open(setmm_nodes, newline="") as f:
            for r in csv.DictReader(f):
                # Closed-form propositional theorems stated with -> and -. only.
                if (r["chapter"] != "Propositional calculus" or r["n_hyps"] != "0"
                        or r["alt_or_old"] != "0" or r["kind"] == "definition"):
                    continue
                try:
                    t = canon(parse_infix(r["statement"]))
                except (ValueError, IndexError):
                    continue        # uses other connectives
                setmm.setdefault(to_polish(t), []).append(r["label"])
    return pm, setmm


def write(u: Universe, out: Path, axiom_spec: str, pm: dict, setmm: dict) -> None:
    out.mkdir(parents=True, exist_ok=True)
    n_der = [0] * len(u)
    n_use = [0] * len(u)
    for c, a, b in u.derivations:
        n_der[c] += 1
        n_use[a] += 1
        n_use[b] += 1
    with open(out / "theorems.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "formula", "readable", "size", "n_vars", "min_steps", "proof",
                    "n_derivations", "n_uses", "pm", "setmm"])
        for i, t in enumerate(u.formulas):
            p = to_polish(t)
            w.writerow([i, p, to_str(t), size(t), len(variables(t)), u.steps[i], u.proof[i],
                        n_der[i], n_use[i], "; ".join(pm.get(p, [])), " ".join(setmm.get(p, []))])
    with open(out / "derivations.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["conclusion", "major", "minor"])
        w.writerows(u.derivations)
    (out / "meta.json").write_text(json.dumps({
        "source": "generated", "axioms": axiom_spec, "max_steps": u.max_steps, "n_axioms": u.n_axioms,
        "n_theorems": len(u), "n_derivations": len(u.derivations),
    }, indent=2) + "\n")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("out", type=Path, help="output directory, e.g. data/gen/luk21")
    ap.add_argument("--max-steps", type=int, default=21)
    ap.add_argument("--axioms", default="lukasiewicz",
                    help="named set (lukasiewicz, implicational) or comma-separated Polish formulas")
    ap.add_argument("--pm", type=Path, default=Path("data/pm/pm_theorems.csv"))
    ap.add_argument("--setmm-nodes", type=Path, default=Path("data/processed/nodes.csv"))
    args = ap.parse_args(argv)
    log = lambda *a: print(*a, file=sys.stderr)
    log(f"axioms: {args.axioms}; horizon: {args.max_steps} steps")
    u = generate(load_axioms(args.axioms), args.max_steps, log)
    pm, setmm = load_names(args.pm, args.setmm_nodes)
    write(u, args.out, args.axioms, pm, setmm)
    found = {to_polish(t) for t in u.formulas}
    log(f"{len(u)} theorems, {len(u.derivations)} derivations -> {args.out}")
    log(f"named theorems inside the horizon: {len(found & pm.keys())} of {len(pm)} Principia formulas, "
        f"{len(found & setmm.keys())} of {len(setmm)} set.mm formulas")


if __name__ == "__main__":
    main()
