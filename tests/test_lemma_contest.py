"""The lemma contest (logicgraph.lemma_contest): tree vs DAG cost with free lemmas."""

import unittest

import numpy as np

from logicgraph.hyperscores import Hypergraph
from logicgraph.lemma_contest import DagCost, TreeCost, cost, greedy


def toy():
    # Axioms 0, 1. 2 = MP(0, 1). 3 = MP(2, 2) reuses 2. 4 = MP(3, 0) or MP(2, 1).
    # 5 = MP(3, 3). 6 = MP(3, 5).
    conc = np.array([2, 3, 4, 5, 4, 6])
    maj = np.array([0, 2, 3, 3, 2, 3])
    mnr = np.array([1, 2, 0, 3, 1, 5])
    steps = np.array([1, 1, 3, 7, 5, 15, 23])
    g = Hypergraph(steps, 2, conc, maj, mnr, max_steps=21)
    return g


class LemmaContestTests(unittest.TestCase):
    def test_tree_naming_matches_reference_solver(self):
        g = toy()
        targets = np.ones(g.n, dtype=bool)
        t = TreeCost(g, targets)
        for free in ([2], [3], [2, 3]):
            ref = g.solve_reference(free=set(free))
            self.assertEqual(t.name(t.base, free).tolist(), ref)

    def test_dag_counts_reused_steps_once(self):
        g = toy()
        targets = np.ones(g.n, dtype=bool)
        d = DagCost(g, targets, np.ones(g.n, dtype=bool))
        self.assertEqual([len(c) for c in d.base], [1, 1, 3, 4, 4, 5, 6])  # tree: 1, 1, 3, 7, 5, 15, 23
        # Naming 2 saves a lot under tree size (it is used twice in 3), little under DAG size.
        tc = TreeCost(g, targets)
        tree_saving = tc.total(tc.base) - tc.total(tc.name(tc.base, [2]))
        dag_saving = d.total(d.base) - d.total(d.name(d.base, [2]))
        self.assertGreater(tree_saving, dag_saving)
        self.assertEqual([len(c) for c in d.name(d.base, [3])], [1, 1, 3, 1, 3, 2, 3])

    def test_dag_never_exceeds_tree_and_is_a_fixed_point(self):
        g = toy()
        d = DagCost(g, np.ones(g.n, dtype=bool), np.ones(g.n, dtype=bool))
        for i, c in enumerate(d.base):
            self.assertLessEqual(len(c), g.L0[i])
            self.assertIn(i, c)
        for c, a, b in zip(d.conc, d.maj, d.mnr):
            self.assertLessEqual(len(d.base[c]), len(d.base[a] | d.base[b] | {c}))

    def test_greedy_lowers_cost(self):
        g = toy()
        t = TreeCost(g, np.ones(g.n, dtype=bool))
        picks, costs = greedy(t, [2, 3, 4], 2, lambda *a: None)
        self.assertEqual(picks[0], 3)                 # 3 is used three times by 6: the best lemma to name
        self.assertLess(cost(t, picks), cost(t, []))
        self.assertEqual(costs[-1], cost(t, picks))


if __name__ == "__main__":
    unittest.main()
