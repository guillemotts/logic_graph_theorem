"""Export nodes, edges and scores as `viz/data.js` for the HTML visualizer.

The data is written as a JS file (`window.GRAPH = {...}`) rather than JSON so
`viz/index.html` also works when opened straight from disk (file://), where
browsers block fetch().

Usage:
    python -m logicgraph.export_viz data/processed viz/data.js
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

KINDS = ["axiom", "definition", "theorem", "axiom_other"]


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("processed", type=Path)
    ap.add_argument("out", type=Path)
    args = ap.parse_args(argv)

    with open(args.processed / "nodes.csv", newline="") as f:
        nodes = list(csv.DictReader(f))
    with open(args.processed / "scores.csv", newline="") as f:
        scores = {r["label"]: r for r in csv.DictReader(f)}
    nodes.sort(key=lambda r: int(r["order"]))
    index = {r["label"]: i for i, r in enumerate(nodes)}

    # Intern repeated strings.
    tables: dict[str, dict[str, int]] = {k: {} for k in ("part", "chapter", "section", "subsection", "contributor")}

    def intern(kind: str, value: str) -> int:
        t = tables[kind]
        if value not in t:
            t[value] = len(t)
        return t[value]

    cols: dict[str, list] = {k: [] for k in (
        "label", "kind", "stmt", "part", "chapter", "section", "subsection", "mathbox", "flags",
        "who", "date", "hyps", "indeg", "outdeg", "reach", "anc", "depth")}
    for r in nodes:
        s = scores[r["label"]]
        flags = (int(r["alt_or_old"]) | int(r["discouraged_usage"]) << 1
                 | int(r["discouraged_proof"]) << 2 | int(r["incomplete"]) << 3)
        cols["label"].append(r["label"])
        cols["kind"].append(KINDS.index(r["kind"]))
        cols["stmt"].append(r["statement"])
        for k in ("part", "chapter", "section", "subsection"):
            cols[k].append(intern(k, r[k]))
        cols["mathbox"].append(int(r["mathbox"]))
        cols["flags"].append(flags)
        cols["who"].append(intern("contributor", r["contributor"]))
        cols["date"].append(r["contributed"])
        cols["hyps"].append(int(r["n_hyps"]))
        cols["indeg"].append(int(s["in_degree"]))
        cols["outdeg"].append(int(s["out_degree"]))
        cols["reach"].append(int(s["reach"]))
        cols["anc"].append(int(s["n_ancestors"]))
        cols["depth"].append(int(s["depth"]))

    # Parents in CSR form: parents of node i are P[PO[i]:PO[i+1]].
    parents: list[list[int]] = [[] for _ in nodes]
    with open(args.processed / "edges.csv", newline="") as f:
        for row in csv.DictReader(f):
            parents[index[row["theorem"]]].append(index[row["lemma"]])
    po, p = [0], []
    for ps in parents:
        p.extend(ps)
        po.append(len(p))

    # Optional outputs of `logicgraph.algorithms` (main library only; null elsewhere).
    algo = {}
    if (args.processed / "algo_nodes.csv").exists():
        with open(args.processed / "algo_nodes.csv", newline="") as f:
            algo = {r["label"]: r for r in csv.DictReader(f)}
        spec = [("pr", "pagerank", float), ("lp", "log10_paths", float), ("com", "community", int),
                ("pin", "part_in", float), ("pout", "part_out", float), ("acut", "art_cut", int), ("dcut", "dom_cut", int)]
        for key, col, typ in spec:
            cols[key] = [typ(algo[r["label"]][col]) if r["label"] in algo else None for r in nodes]
    extras = {}
    for name in ("communities", "percolation"):
        path = args.processed / f"{name}.csv"
        if path.exists():
            with open(path, newline="") as f:
                extras[name] = list(csv.DictReader(f))

    # Optional outputs of the generator track (`logicgraph.gen_export`).
    if (args.processed / "gen_scores.csv").exists():
        with open(args.processed / "gen_scores.csv", newline="") as f:
            gen = {r["label"]: r for r in csv.DictReader(f)}
        num = lambda typ: (lambda x: typ(x) if x != "" else None)
        for key, col, conv in [("gain", "gain", num(float)), ("ko", "knockout", num(float)),
                               ("lost", "lost", num(float)), ("deep", "deep", num(float)),
                               ("nder", "n_derivations", num(int)), ("steps", "min_steps", num(int)),
                               ("proof", "proof", str), ("sub", "subsumed_by", str), ("logic", "logic", str)]:
            cols[key] = [conv(gen[r["label"]][col]) for r in nodes]
        # Supernode columns: sn<k> representative label, sm<k> members, sg<k> gain, sk<k> knockout.
        first = next(iter(gen.values()))
        for k in (1, 2, 3):
            if f"sn{k}" not in first:
                continue
            cols[f"sn{k}"] = [gen[r["label"]][f"sn{k}"] for r in nodes]
            for c in ("sm", "sg", "sk"):
                cols[f"{c}{k}"] = [num(float)(gen[r["label"]][f"{c}{k}"]) for r in nodes]
    meta = {"source": "setmm"}
    if (args.processed / "meta.json").exists():
        meta = json.loads((args.processed / "meta.json").read_text())

    data = {
        "meta": meta,
        "extras": extras,
        "kinds": KINDS,
        "names": {k: list(t) for k, t in tables.items()},
        "nodes": cols,
        "PO": po,
        "P": p,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        f.write("window.GRAPH = ")
        json.dump(data, f, separators=(",", ":"))
        f.write(";\n")
    print(f"{len(nodes)} nodes, {len(p)} edges -> {args.out} ({args.out.stat().st_size / 1e6:.1f} MB)",
          file=sys.stderr)


if __name__ == "__main__":
    main()
