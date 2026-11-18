import unittest

import numpy as np

from logicgraph import formula as F
from logicgraph.generate import generate
from logicgraph.hyperscores import Hypergraph
from logicgraph.transfer import partial_spearman, saving

N, B = 15, 11      # hypergraph horizon, library bound


class TransferTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        u = generate(F.axioms("lukasiewicz"), N)
        d = np.array(u.derivations, dtype=np.int32)
        cls.u = u
        cls.g = Hypergraph(np.array(u.steps, dtype=np.int32), u.n_axioms, d[:, 0], d[:, 1], d[:, 2], N)
        cls.lib = {F.to_polish(t): s for t, s in zip(u.formulas, u.steps) if s <= B}

    def test_existing_axiom_saves_nothing(self):
        self.assertEqual(saving("lukasiewicz", self.lib, B, "CpCqp"), (0, 0))

    def test_regeneration_finds_at_least_what_the_hypergraph_finds(self):
        # Naming v on the fixed hypergraph only sees proofs whose expansion fits in N steps,
        # so its savings are a lower bound on the exact (regenerated) savings.
        g, u = self.g, self.u
        for v in np.flatnonzero((g.L0 > 1) & (g.L0 <= 7)).tolist()[:12]:
            f = F.to_polish(u.formulas[v])
            L = g.solve_reference(free={v})
            lower = sum(g.L0[t] - L[t] for t in range(g.n) if g.L0[t] <= B and t != v)
            exact, improved = saving("lukasiewicz", self.lib, B, f)
            self.assertGreaterEqual(exact, lower, F.to_str(u.formulas[v]))
            self.assertLessEqual(improved, len(self.lib))

    def test_identity_helps_little_in_its_own_system(self):
        # p -> p: a free identity shortens only proofs that used it as a step.
        s, n = saving("lukasiewicz", self.lib, B, "Cpp")
        self.assertGreater(s, 0)
        self.assertLess(n, len(self.lib))

    def test_partial_spearman_removes_a_shared_cause(self):
        rng = np.random.default_rng(0)
        z = rng.normal(size=500)
        x, y = z + 0.1 * rng.normal(size=500), z + 0.1 * rng.normal(size=500)
        self.assertGreater(np.corrcoef(x, y)[0, 1], 0.9)
        self.assertLess(abs(partial_spearman(x, y, z)), 0.2)


if __name__ == "__main__":
    unittest.main()
