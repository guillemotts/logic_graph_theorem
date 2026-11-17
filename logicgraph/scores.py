"""Basic structural scores on the dependency graph.

These only need the edge list (which lemmas a proof uses), not proof
multiplicities, so they work straight off `parse_setmm` output.

  in_degree    number of theorems whose proof cites this one directly
  out_degree   number of distinct lemmas this proof cites directly
  reach        number of theorems that depend on this one, transitively
  n_ancestors  number of statements this one depends on, transitively
  depth        longest chain of citations down to an axiom/definition
  axioms       the `ax-*` axioms this theorem transitively depends on

File order in set.mm is a topological order (every label is declared before
it is used), so each score is a single pass in order or reverse order.

Usage:
    python -m logicgraph.scores data/processed
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path


def load(processed: Path) -> tuple[list[dict], list[list[int]]]:
    with open(processed / "nodes.csv", newline="") as f:
        nodes = list(csv.DictReader(f))
    index = {row["label"]: i for i, row in enumerate(nodes)}
    parents: list[list[int]] = [[] for _ in nodes]
    with open(processed / "edges.csv", newline="") as f:
        for row in csv.DictReader(f):
            parents[index[row["theorem"]]].append(index[row["lemma"]])
    return nodes, parents


def compute(nodes: list[dict], parents: list[list[int]]) -> list[dict]:
    n = len(nodes)
    order = sorted(range(n), key=lambda i: int(nodes[i]["order"]))
    pos = {v: k for k, v in enumerate(order)}
    for v in range(n):
        assert all(pos[p] < pos[v] for p in parents[v]), "file order is not topological"

    children: list[list[int]] = [[] for _ in range(n)]
    for v, ps in enumerate(parents):
        for p in ps:
            children[p].append(v)

    axioms = [i for i, row in enumerate(nodes) if row["kind"] == "axiom"]
    ax_bit = {v: 1 << k for k, v in enumerate(axioms)}

    # Forward pass: ancestors (as an int bitset), axiom bitset, depth.
    n_anc = [0] * n
    ax_set = [0] * n
    depth = [0] * n
    anc: list[int] = [0] * n
    for v in order:
        a = 0
        ax = ax_bit.get(v, 0)
        d = 0
        for p in parents[v]:
            a |= anc[p] | (1 << p)
            ax |= ax_set[p]
            d = max(d, depth[p] + 1)
        anc[v], ax_set[v], depth[v] = a, ax, d
        n_anc[v] = a.bit_count()
    del anc

    # Backward pass: descendants.
    reach = [0] * n
    desc: list[int] = [0] * n
    for v in reversed(order):
        s = 0
        for c in children[v]:
            s |= desc[c] | (1 << c)
        desc[v] = s
        reach[v] = s.bit_count()
    del desc

    out = []
    for v, row in enumerate(nodes):
        names = [nodes[axioms[k]]["label"] for k in range(len(axioms)) if ax_set[v] >> k & 1]
        out.append({
            "label": row["label"],
            "in_degree": len(children[v]),
            "out_degree": len(parents[v]),
            "reach": reach[v],
            "n_ancestors": n_anc[v],
            "depth": depth[v],
            "n_axioms": len(names),
            "axioms": " ".join(names),
        })
    return out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("processed", type=Path, help="directory with nodes.csv and edges.csv")
    args = ap.parse_args(argv)
    nodes, parents = load(args.processed)
    rows = compute(nodes, parents)
    with open(args.processed / "scores.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    print(f"scores for {len(rows)} nodes -> {args.processed / 'scores.csv'}", file=sys.stderr)


if __name__ == "__main__":
    main()
