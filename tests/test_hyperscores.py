import unittest

import numpy as np

from logicgraph import formula as F
from logicgraph.generate import generate
from logicgraph.hyperscores import BIG, Hypergraph

AX = F.axioms("lukasiewicz")


def build(max_steps: int) -> tuple:
    u = generate(AX, max_steps)
    d = np.array(u.derivations, dtype=np.int32)
    g = Hypergraph(np.array(u.steps, dtype=np.int32), u.n_axioms, d[:, 0], d[:, 1], d[:, 2], max_steps)
    return u, g


class HyperscoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.u, cls.g = build(11)
        cls.targets = cls.g.L0 <= 9

    def test_baseline_matches_generation(self):
        self.assertEqual(self.g.solve_reference(), self.g.L0.tolist())

    def test_fast_solver_matches_reference(self):
        g = self.g
        # Every theorem provable in <= 7 steps, plus the axioms.
        for v in np.flatnonzero(g.L0 <= 7).tolist():
            _, banned = g.resolve(v, "ban")
            self.assertEqual(np.minimum(banned, BIG).tolist(), g.solve_reference(banned={v}), f"ban {v}")
            if v >= g.n_axioms:
                _, named = g.resolve(v, "name")
                self.assertEqual(named.tolist(), g.solve_reference(free={v}), f"name {v}")

    def test_monotone(self):
        g = self.g
        for v in np.flatnonzero((g.L0 > 1) & (g.L0 <= 9)).tolist():
            _, banned = g.resolve(v, "ban")
            _, named = g.resolve(v, "name")
            rest = np.arange(g.n) != v
            self.assertTrue((banned[rest] >= g.L0[rest]).all())
            self.assertTrue((named[rest] <= g.L0[rest]).all())

    def test_without_any_axiom_nothing_is_provable(self):
        g = self.g
        L = g.solve_reference(banned=set(range(g.n_axioms)))
        self.assertTrue(all(x >= BIG for x in L))

    def test_identity_needs_axiom_one_and_two(self):
        # p -> p is DD211: inside the horizon it cannot be proved without ax-1 or without ax-2.
        g, ident = self.g, self.u.formulas.index((0, 0))
        for axiom in (0, 1):
            _, L = g.resolve(axiom, "ban")
            self.assertGreater(L[ident], g.N)
        _, L = g.resolve(2, "ban")
        self.assertEqual(L[ident], 5)       # ax-3 is not needed

    def test_identity_scores(self):
        g, ident = self.g, self.u.formulas.index((0, 0))
        s = g.score(ident, self.targets)
        self.assertGreater(s["saving"], 0)
        self.assertGreaterEqual(s["knockout"], s["affected"])
        self.assertGreaterEqual(s["affected"], s["lost"])


if __name__ == "__main__":
    unittest.main()
