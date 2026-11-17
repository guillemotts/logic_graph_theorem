"""Graph algorithms on the theorem dependency graph.

Runs on the main library by default (mathboxes and *ALT/*OLD proofs dropped).
Edges point lemma -> theorem ("was used to prove").

Separation ("what breaks if I remove X?")
  art_cut        Undirected cut vertices: nodes that are no longer in the main
                 body of the graph once X is deleted.
  bridges        Undirected bridges: edges whose removal splits the graph, with
                 the size of the smaller side.
  dom_cut        Dominator tree from the axioms ("any path suffices" / OR reading):
                 theorems that lose every path from the axioms when X is deleted.
                 A citation edge u -> t is critical exactly when u is t's only
                 lemma; then it cuts off t's whole dominator subtree.
  percolation    Delete nodes in order (most cited first, most reach first, random)
                 and track the largest undirected connected component.
  glue_components  The components left after deleting the top-K most cited lemmas.

Centrality and structure
  pagerank       PageRank with importance flowing from a theorem to the lemmas it cites.
  log10_paths    log10 of the number of axiom->leaf dependency chains through a node;
                 path_frac is the fraction of all such chains.
  community      Louvain communities on the undirected graph, each citation weighted
                 by 1 / (times the lemma is cited) so glue lemmas don't dominate.
  part_in        Participation coefficient over a theorem's lemmas (0 = all from one
                 community; high = its proof draws on several areas).
  part_out       Participation coefficient over a lemma's citers (high = used across areas).

Usage:
    python -m logicgraph.algorithms data/processed [--include-mathboxes] [--glue-k 300]
"""

from __future__ import annotations

import argparse
import csv
import math
import random
import sys
import time
from collections import Counter
from pathlib import Path

import networkx as nx
import numpy as np
import scipy.sparse as sp
from sklearn.metrics import adjusted_rand_score, normalized_mutual_info_score


# ---------------------------------------------------------------- loading

class Graph:
    """Dependency DAG with nodes 0..n-1 in file (= topological) order."""

    def __init__(self, nodes: list[dict], edges: list[tuple[int, int]]):
        self.nodes = nodes
        self.n = len(nodes)
        self.label = [r["label"] for r in nodes]
        self.parents: list[list[int]] = [[] for _ in range(self.n)]
        self.children: list[list[int]] = [[] for _ in range(self.n)]
        for u, v in edges:
            self.parents[v].append(u)
            self.children[u].append(v)
        self.edges = edges
        self.adj = [p + c for p, c in zip(self.parents, self.children)]  # undirected
        self.indeg = [len(c) for c in self.children]   # "cited by"


def load(processed: Path, include_mathboxes: bool) -> Graph:
    with open(processed / "nodes.csv", newline="") as f:
        rows = sorted(csv.DictReader(f), key=lambda r: int(r["order"]))
    keep = [r for r in rows if r["alt_or_old"] == "0" and (include_mathboxes or r["mathbox"] == "0")]
    index = {r["label"]: i for i, r in enumerate(keep)}
    edges = []
    with open(processed / "edges.csv", newline="") as f:
        for r in csv.DictReader(f):
            u, v = index.get(r["lemma"]), index.get(r["theorem"])
            if u is not None and v is not None:
                edges.append((u, v))
    return Graph(keep, edges)


# ---------------------------------------------------------------- separation

def cut_vertices_and_bridges(g: Graph) -> tuple[list[int], list[tuple[int, int, int]]]:
    """Tarjan's low-link DFS (iterative) with subtree sizes.

    Returns art_cut[v] = nodes separated from the largest remaining piece when v
    is deleted, and bridges as (u, v, size of the smaller side).
    """
    n, adj = g.n, g.adj
    disc = [-1] * n
    low = [0] * n
    sub = [1] * n
    parent = [-1] * n
    pieces: list[list[int]] = [[] for _ in range(n)]
    art_cut = [0] * n
    bridges: list[tuple[int, int, int]] = []
    t = 0
    for s in range(n):
        if disc[s] != -1:
            continue
        comp = []
        disc[s] = low[s] = t; t += 1
        stack = [(s, 0)]
        comp.append(s)
        pending_bridges = []
        while stack:
            v, i = stack[-1]
            if i < len(adj[v]):
                stack[-1] = (v, i + 1)
                u = adj[v][i]
                if disc[u] == -1:
                    parent[u] = v
                    disc[u] = low[u] = t; t += 1
                    comp.append(u)
                    stack.append((u, 0))
                elif u != parent[v]:
                    low[v] = min(low[v], disc[u])
            else:
                stack.pop()
                p = parent[v]
                if p != -1:
                    sub[p] += sub[v]
                    low[p] = min(low[p], low[v])
                    if low[v] >= disc[p] or p == s:
                        pieces[p].append(sub[v])
                    if low[v] > disc[p]:
                        pending_bridges.append((p, v, sub[v]))
        size = len(comp)
        for v in comp:
            ps = pieces[v]
            if not ps or (v == s and len(ps) < 2):
                continue
            rest = size - 1 - sum(ps)
            art_cut[v] = size - 1 - max(ps + [rest])
        for p, v, sv in pending_bridges:
            bridges.append((p, v, min(sv, size - sv)))
    bridges.sort(key=lambda b: -b[2])
    return art_cut, bridges


def dominators(g: Graph) -> tuple[list[int], list[int]]:
    """Immediate dominators from a virtual root above every parentless node.

    On a DAG processed in topological order, idom(v) is the nearest common
    dominator-tree ancestor of v's parents (Cooper-Harvey-Kennedy, one pass).
    Returns idom (-1 = root) and dom_cut[v] = size of v's dominator subtree - 1.
    """
    n = g.n
    root = n
    idom = [root] * (n + 1)
    depth = [0] * (n + 1)

    def meet(a: int, b: int) -> int:
        while a != b:
            if depth[a] > depth[b]:
                a = idom[a]
            elif depth[b] > depth[a]:
                b = idom[b]
            else:
                a, b = idom[a], idom[b]
        return a

    for v in range(n):
        ps = g.parents[v]
        if not ps:
            idom[v] = root
        else:
            d = ps[0]
            for p in ps[1:]:
                if d == root:
                    break
                d = meet(d, p)
            idom[v] = d
        depth[v] = depth[idom[v]] + 1
    size = [1] * n
    for v in range(n - 1, -1, -1):
        if idom[v] != root:
            size[idom[v]] += size[v]
    return [-1 if idom[v] == root else idom[v] for v in range(n)], [s - 1 for s in size]


def percolation(g: Graph, order: list[int]) -> list[int]:
    """lcc[k] = largest undirected component after deleting order[:k] (Newman-Ziff)."""
    n = g.n
    up = list(range(n))
    sz = [1] * n
    active = [False] * n

    def find(x: int) -> int:
        while up[x] != x:
            up[x] = up[up[x]]
            x = up[x]
        return x

    lcc = [0] * (n + 1)
    best = 0
    for j, v in enumerate(reversed(order), start=1):
        active[v] = True
        rv = find(v)
        for u in g.adj[v]:
            if active[u]:
                ru = find(u)
                if ru != rv:
                    if sz[ru] > sz[rv]:
                        ru, rv = rv, ru
                    up[ru] = rv
                    sz[rv] += sz[ru]
        best = max(best, sz[find(v)])
        lcc[n - j] = best
    return lcc


def components_without(g: Graph, removed: set[int]) -> list[list[int]]:
    seen = [False] * g.n
    comps = []
    for s in range(g.n):
        if seen[s] or s in removed:
            continue
        seen[s] = True
        comp, stack = [s], [s]
        while stack:
            v = stack.pop()
            for u in g.adj[v]:
                if not seen[u] and u not in removed:
                    seen[u] = True
                    comp.append(u)
                    stack.append(u)
        comps.append(comp)
    comps.sort(key=len, reverse=True)
    return comps


# ---------------------------------------------------------------- centrality

def pagerank(g: Graph, d: float = 0.85, tol: float = 1e-10) -> np.ndarray:
    """Importance flows theorem -> lemmas it cites (like citations)."""
    n = g.n
    src = np.fromiter((v for u, v in g.edges), dtype=np.int64, count=len(g.edges))   # theorem
    dst = np.fromiter((u for u, v in g.edges), dtype=np.int64, count=len(g.edges))   # lemma
    outdeg = np.bincount(src, minlength=n).astype(float)
    w = 1.0 / outdeg[src]
    M = sp.csr_matrix((w, (dst, src)), shape=(n, n))
    dangling = outdeg == 0
    r = np.full(n, 1.0 / n)
    for _ in range(200):
        r2 = d * (M @ r + r[dangling].sum() / n) + (1 - d) / n
        if np.abs(r2 - r).sum() < tol:
            return r2
        r = r2
    return r


def path_counts(g: Graph) -> tuple[list[float], list[float]]:
    """Exact counts of source->sink dependency chains through each node (big ints)."""
    n = g.n
    n_in = [0] * n
    for v in range(n):
        n_in[v] = sum(n_in[p] for p in g.parents[v]) if g.parents[v] else 1
    n_out = [0] * n
    for v in range(n - 1, -1, -1):
        n_out[v] = sum(n_out[c] for c in g.children[v]) if g.children[v] else 1
    total = sum(n_in[v] for v in range(n) if not g.children[v])
    log_total = math.log10(total)
    logs = [math.log10(n_in[v] * n_out[v]) for v in range(n)]
    return logs, [10 ** (l - log_total) for l in logs]


def communities(g: Graph, seed: int = 0, resolution: float = 1.0,
                weighting: str = "inv_indeg") -> tuple[list[int], list[float], list[float]]:
    """Louvain communities; returns community ids and two participation coefficients.

    part_in  spread of a theorem's *lemmas* over communities: high = its proof
             combines results from several areas (a "synthesis" theorem).
    part_out spread of a lemma's *citers* over communities: high = used across
             areas. Glue lemmas (syl, adantr, ...) top this trivially.

    weighting="inv_indeg" gives a citation u -> t weight 1 / (times u is cited),
    so glue lemmas like `syl` (cited 15k times) barely count while a rare lemma
    shared by two theorems is strong evidence they belong together. Unweighted
    ("plain") Louvain groups theorems by proof style (deduction vs closed form)
    instead of topic.
    """
    def weight(u: int) -> float:
        return 1.0 / g.indeg[u] if weighting == "inv_indeg" else 1.0

    G = nx.Graph()
    G.add_nodes_from(range(g.n))
    G.add_weighted_edges_from((u, v, weight(u)) for u, v in g.edges)
    comms = nx.community.louvain_communities(G, weight="weight", seed=seed, resolution=resolution)
    comms.sort(key=len, reverse=True)
    cid = [0] * g.n
    for k, c in enumerate(comms):
        for v in c:
            cid[v] = k
    # Weighted participation coefficient: 1 - sum_c (strength into c / total strength)^2.
    def participation(pairs) -> float:
        acc: Counter = Counter()
        for c, w in pairs:
            acc[c] += w
        tot = sum(acc.values())
        return 1.0 - sum((x / tot) ** 2 for x in acc.values()) if tot else 0.0

    part_in = [participation((cid[u], weight(u)) for u in g.parents[v]) for v in range(g.n)]
    part_out = [participation((cid[c], 1.0) for c in g.children[v]) for v in range(g.n)]
    return cid, part_in, part_out


# ---------------------------------------------------------------- report

def describe(g: Graph, comp: list[int], key: str = "chapter") -> tuple[str, float, str]:
    """Dominant chapter, its share, and the members most cited from *inside* the set.

    Ranking by citations from inside the set (not global in-degree) keeps glue
    lemmas like `syl` from being every group's "representative".
    """
    cnt = Counter(g.nodes[v][key] for v in comp)
    top, k = cnt.most_common(1)[0]
    members = set(comp)
    inside = {v: sum(1 for c in g.children[v] if c in members) for v in comp}
    ex = sorted(comp, key=lambda v: (-inside[v], -g.indeg[v]))[:5]
    return top, k / len(comp), " ".join(g.label[v] for v in ex)


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("processed", type=Path)
    ap.add_argument("--include-mathboxes", action="store_true")
    ap.add_argument("--glue-k", type=int, default=300, help="most-cited lemmas to delete for glue_components")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args(argv)
    out = args.processed
    log = lambda *a: print(*a, file=sys.stderr)
    clock = time.time()

    g = load(out, args.include_mathboxes)
    log(f"graph: {g.n} nodes, {len(g.edges)} edges")

    art_cut, bridges = cut_vertices_and_bridges(g)
    log(f"cut vertices/bridges ({time.time() - clock:.1f}s)")
    idom, dom_cut = dominators(g)
    log(f"dominators ({time.time() - clock:.1f}s)")
    pr = pagerank(g)
    logp, pfrac = path_counts(g)
    log(f"pagerank, path counts ({time.time() - clock:.1f}s)")
    cid, part_in, part_out = communities(g, seed=args.seed)
    cid_plain, _, _ = communities(g, seed=args.seed, weighting="plain")
    log(f"louvain: {max(cid) + 1} communities ({time.time() - clock:.1f}s)")

    # Percolation curves.
    by_indeg = sorted(range(g.n), key=lambda v: -g.indeg[v])
    reach = [0] * g.n
    with open(out / "scores.csv", newline="") as f:
        sc = {r["label"]: int(r["reach"]) for r in csv.DictReader(f)}
    reach = [sc[l] for l in g.label]
    by_reach = sorted(range(g.n), key=lambda v: -reach[v])
    curves = {"most_cited": percolation(g, by_indeg), "most_reach": percolation(g, by_reach)}
    rng = random.Random(args.seed)
    rnd = np.zeros(g.n + 1)
    for _ in range(5):
        o = list(range(g.n)); rng.shuffle(o)
        rnd += np.array(percolation(g, o))
    curves["random"] = list(rnd / 5)
    log(f"percolation ({time.time() - clock:.1f}s)")

    # ---- write tables
    with open(out / "algo_nodes.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["label", "art_cut", "dom_cut", "idom", "pagerank", "log10_paths", "path_frac",
                    "community", "part_in", "part_out"])
        for v in range(g.n):
            w.writerow([g.label[v], art_cut[v], dom_cut[v], g.label[idom[v]] if idom[v] >= 0 else "",
                        f"{pr[v]:.6g}", f"{logp[v]:.3f}", f"{pfrac[v]:.6g}", cid[v], f"{part_in[v]:.4f}", f"{part_out[v]:.4f}"])

    with open(out / "algo_bridges.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["lemma", "theorem", "smaller_side"])
        for u, v, s in bridges:
            a, b = (u, v) if u < v else (v, u)
            w.writerow([g.label[a], g.label[b], s])

    crit = [(g.parents[v][0], v, dom_cut[v] + 1) for v in range(g.n) if len(g.parents[v]) == 1]
    crit.sort(key=lambda e: -e[2])
    with open(out / "algo_critical_edges.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["lemma", "theorem", "cut_off"])
        for u, v, s in crit:
            w.writerow([g.label[u], g.label[v], s])

    ks = sorted({*range(0, 101, 5), *range(100, 1001, 50), *range(1000, g.n + 1, 500), g.n})
    with open(out / "percolation.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["removed", *curves])
        for k in ks:
            w.writerow([k, *(int(round(c[k])) for c in curves.values())])

    removed = set(by_indeg[:args.glue_k])
    comps = components_without(g, removed)
    with open(out / "glue_components.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["component", "size", "top_chapter", "purity", "most_cited_members"])
        for k, c in enumerate(comps):
            if len(c) < 5:
                break
            w.writerow([k, len(c), *describe(g, c)])

    groups: dict[int, list[int]] = {}
    for v, c in enumerate(cid):
        groups.setdefault(c, []).append(v)
    with open(out / "communities.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["community", "size", "top_chapter", "purity", "most_cited_members"])
        for c in sorted(groups):
            w.writerow([c, len(groups[c]), *describe(g, groups[c])])

    # ---- console report
    chap = [r["chapter"] for r in g.nodes]
    sect = [r["chapter"] + "/" + r["section"] for r in g.nodes]
    for name, c in (("1/indeg-weighted", cid), ("unweighted", cid_plain)):
        log(f"\nLouvain {name}: {max(c) + 1} communities, NMI vs chapter={normalized_mutual_info_score(chap, c):.3f} "
            f"ARI={adjusted_rand_score(chap, c):.3f}, NMI vs section={normalized_mutual_info_score(sect, c):.3f}")
    log(f"bridges: {len(bridges)}, largest smaller side: {bridges[0][2] if bridges else 0}")
    log(f"cut vertices: {sum(1 for x in art_cut if x)}, max cut-off: {max(art_cut)}")
    log(f"dominator-critical edges: {len(crit)}, max cut-off: {crit[0][2] if crit else 0}")
    log(f"after deleting top {args.glue_k} cited: {len(comps)} components, largest {len(comps[0])} "
        f"({len(comps[0]) / (g.n - args.glue_k):.1%} of rest)")
    log(f"done in {time.time() - clock:.1f}s")


if __name__ == "__main__":
    main()
