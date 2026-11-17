"""Put a generated universe into the visualizer.

Writes the scored library (theorems with L <= N - slack) in the same
nodes.csv / edges.csv schema the set.mm pipeline uses, then runs the existing
`scores` and `export_viz` steps on it. Open the result with `viz/index.html?data=gen`.

  label     set.mm label or Principia number when the theorem has one, else t<id>
  chapter   "<n> steps" (shortest proof length), so the overview groups by length
  section   Principia names
  edges     the two premises of one shortest derivation of each theorem
  alt_or_old flag is reused for "redundant instance of a shorter theorem"

Usage:
    python -m logicgraph.gen_export data/gen/luk21 viz/data_gen.js
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

from . import export_viz, scores
from .formula import parse_polish, to_setmm


def label_for(t: dict, n_axioms: int) -> str:
    i = int(t["id"])
    if i < n_axioms:
        return f"ax-{i + 1}"
    if t["setmm"]:
        return t["setmm"].split()[0]
    if t["pm"]:
        return "pm" + t["pm"].split(";")[0].split()[0].lstrip("*")
    return f"t{i}"


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run", type=Path, help="directory with theorems.csv, derivations.csv, scores.csv")
    ap.add_argument("out", type=Path, help="JS data file for the visualizer, e.g. viz/data_gen.js")
    args = ap.parse_args(argv)
    meta = json.loads((args.run / "meta.json").read_text())

    with open(args.run / "scores.csv", newline="") as f:
        sc = {int(r["id"]): r for r in csv.DictReader(f)}
    # The library: everything short enough to be a target, redundant instances included (flagged).
    limit = max(int(r["min_steps"]) for r in sc.values() if r["is_target"] == "1")
    with open(args.run / "theorems.csv", newline="") as f:
        theorems = [t for t in csv.DictReader(f) if int(t["min_steps"]) <= limit]
    labels: dict[int, str] = {}
    used: set[str] = set()
    for t in theorems:
        lab = label_for(t, meta["n_axioms"])
        if lab in used:
            lab = f"{lab}-t{t['id']}"
        used.add(lab)
        labels[int(t["id"])] = lab

    out = args.run / "viz"
    out.mkdir(exist_ok=True)
    axiom_names = ", ".join(f"ax-{k + 1}" for k in range(meta["n_axioms"]))
    with open(out / "nodes.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["label", "kind", "order", "statement", "n_symbols", "n_hyps", "part", "chapter", "section",
                    "subsection", "mathbox", "alt_or_old", "discouraged_usage", "discouraged_proof",
                    "contributor", "contributed", "proof_format", "incomplete", "n_uses"])
        for t in theorems:
            i = int(t["id"])
            w.writerow([labels[i], "axiom" if i < meta["n_axioms"] else "theorem", i,
                        to_setmm(parse_polish(t["formula"])),
                        t["size"], 0, f"Generated from {axiom_names}", f"{int(t['min_steps'])} steps", t["pm"], "",
                        0, int(sc[i]["subsumed_by"] != ""), 0, 0, "", "", "", 0, t["n_uses"]])

    # One shortest derivation per theorem: the first one on file (generation records it first).
    first: dict[int, tuple[int, int]] = {}
    with open(args.run / "derivations.csv", newline="") as f:
        for r in csv.DictReader(f):
            c = int(r["conclusion"])
            if c in labels and c >= meta["n_axioms"] and c not in first:
                first[c] = (int(r["major"]), int(r["minor"]))
    with open(out / "edges.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["lemma", "theorem"])
        for c, (a, b) in first.items():
            for p in dict.fromkeys((a, b)):
                w.writerow([labels[p], labels[c]])

    # Supernodes (logicgraph.supernodes), if computed: each theorem's supernode at every
    # level, and the supernode scores on the representative's row.
    sn: dict[int, dict] = {}
    sn_scores: dict[tuple[int, int], dict] = {}
    if (args.run / "supernodes.csv").exists():
        with open(args.run / "supernodes.csv", newline="") as f:
            sn = {int(r["id"]): r for r in csv.DictReader(f)}
        with open(args.run / "supernode_scores.csv", newline="") as f:
            sn_scores = {(int(r["level"]), int(r["supernode"])): r for r in csv.DictReader(f)}
    levels = (1, 2, 3) if sn else ()
    # Weakest logic proving each theorem (logicgraph.logicmap), if computed.
    tags: dict[int, str] = {}
    if (args.run / "logic_tags.csv").exists():
        with open(args.run / "logic_tags.csv", newline="") as f:
            tags = {int(r["id"]): r["logic"] for r in csv.DictReader(f)}
    with open(out / "gen_scores.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["label", "gain", "knockout", "lost", "deep", "n_derivations", "min_steps", "proof", "subsumed_by", "logic",
                    *(f"{c}{k}" for k in levels for c in ("sn", "sm", "sg", "sk"))])
        for t in theorems:
            i = int(t["id"])
            s = sc[i]
            extra = []
            for k in levels:
                rep = int(sn[i][f"level{k}"])
                r = sn_scores[(k, rep)] if rep == i else None
                extra += [labels[rep], r["n_members"] if r else "", r["gain"] if r else "", r["knockout"] if r else ""]
            w.writerow([labels[i], s["gain"], s["knockout"], s["lost"], s["deep"], t["n_derivations"],
                        t["min_steps"], t["proof"], labels.get(int(s["subsumed_by"]), "") if s["subsumed_by"] else "",
                        tags.get(i, ""), *extra])

    (out / "meta.json").write_text(json.dumps({**meta, "library_steps": limit, "library_size": len(theorems)}) + "\n")
    scores.main([str(out)])
    export_viz.main([str(out), str(args.out)])
    print(f"open viz/index.html?data=gen ({len(theorems)} theorems with proofs of <= {limit} steps)", file=sys.stderr)


if __name__ == "__main__":
    main()
