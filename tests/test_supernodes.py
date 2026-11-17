import unittest

import numpy as np

from logicgraph import formula as F
from logicgraph.generate import generate
from logicgraph.hyperscores import BIG, Hypergraph
from logicgraph.subsumption import redundant
from logicgraph.supernodes import SupernodeScorer, build_levels, exchange_key, weakening_key

AX = F.axioms("lukasiewicz")
P = F.parse_polish


class KeyTests(unittest.TestCase):
    def test_weakening_drops_leading_dummy_hypotheses(self):
        self.assertEqual(weakening_key(P("CpCqCrq")), weakening_key(P("CpCqp")))     # ax1w ~ ax-1
        self.assertEqual(weakening_key(P("CpCqq")), weakening_key(P("Cpp")))         # idd ~ id
        self.assertNotEqual(weakening_key(P("CpCqp")), weakening_key(P("Cpp")))      # ax-1 is not id here
        self.assertNotEqual(weakening_key(P("CpCpp")), weakening_key(P("Cpp")))      # p is not fresh

    def test_exchange_ignores_hypothesis_order(self):
        syll1 = P("CCqrCCpqCpr")        # *2.05 (q -> r) -> ((p -> q) -> (p -> r))
        syll2 = P("CCpqCCqrCpr")        # *2.06 (p -> q) -> ((q -> r) -> (p -> r))
        self.assertEqual(exchange_key(syll1), exchange_key(syll2))
        self.assertEqual(exchange_key(P("CNpCpq")), exchange_key(P("CpCNpq")))      # *2.21 ~ *2.24
        # Fresh hypotheses anywhere are dropped, so ax-1 joins p -> p at this level.
        self.assertEqual(exchange_key(P("CpCqp")), exchange_key(P("Cpp")))
        self.assertNotEqual(exchange_key(P("CCpqCpq")), exchange_key(P("Cpp")))


class LevelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.u = generate(AX, 15)
        u = cls.u
        lib = [i for i, s in enumerate(u.steps) if s <= 11]
        red = redundant([u.formulas[i] for i in lib], [u.steps[i] for i in lib])
        cls.subsumed_by = {i: j for i, j in enumerate(red) if j is not None}
        cls.levels = build_levels({i: u.formulas[i] for i in lib}, {i: u.steps[i] for i in lib},
                                  {i: F.size(u.formulas[i]) for i in lib}, cls.subsumed_by)

    def test_levels_nest_and_shrink(self):
        counts = [len(set(self.levels[k].values())) for k in (1, 2, 3)]
        self.assertGreater(counts[0], counts[1])
        self.assertGreater(counts[1], counts[2])
        for k in (2, 3):
            for i, r in self.levels[k].items():
                # Members of one lower-level supernode stay together.
                self.assertEqual(self.levels[k][self.levels[k - 1][i]], r)

    def test_representatives_are_most_general_and_cheapest(self):
        u = self.u
        for k in (1, 2, 3):
            for i, r in self.levels[k].items():
                self.assertNotIn(r, self.subsumed_by)
                self.assertLessEqual(u.steps[r], u.steps[i])
        for i, r in self.levels[1].items():
            self.assertTrue(F.subsumes(u.formulas[r], u.formulas[i]))

    def test_named_merges(self):
        ids = {F.to_polish(t): i for i, t in enumerate(self.u.formulas)}
        lv = self.levels
        self.assertEqual(lv[2][ids["CpCqCrq"]], lv[2][ids["CpCqp"]])      # ax1w joins ax-1 at level 2
        self.assertNotEqual(lv[1][ids["CpCqCrq"]], lv[1][ids["CpCqp"]])
        self.assertEqual(lv[3][ids["CpCqp"]], lv[3][ids["Cpp"]])          # ax-1 joins id only at level 3
        self.assertNotEqual(lv[2][ids["CpCqp"]], lv[2][ids["Cpp"]])


class SetSolverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        u = generate(AX, 11)
        d = np.array(u.derivations, dtype=np.int32)
        cls.u = u
        cls.g = Hypergraph(np.array(u.steps, dtype=np.int32), u.n_axioms, d[:, 0], d[:, 1], d[:, 2], 11)

    def test_sets_match_reference_solver(self):
        g, rng = self.g, np.random.default_rng(0)
        pool = np.flatnonzero((g.L0 > 1) & (g.L0 <= 7))
        for _ in range(25):
            vs = rng.choice(pool, size=3, replace=False)
            _, banned = g.resolve(vs, "ban")
            self.assertEqual(np.minimum(banned, BIG).tolist(), g.solve_reference(banned=set(vs.tolist())))
            _, named = g.resolve(vs, "name")
            self.assertEqual(named.tolist(), g.solve_reference(free=set(vs.tolist())))

    def test_singleton_supernodes_reproduce_theorem_scores(self):
        g = self.g
        targets = g.L0 <= 9
        scorer = SupernodeScorer(g, {i: i for i in np.flatnonzero(targets).tolist()})
        for v in np.flatnonzero((g.L0 > 1) & (g.L0 <= 7)).tolist():
            self.assertEqual(scorer.score(v), g.score(v, targets), f"theorem {v}")

    def test_banning_a_supernode_hurts_at_least_as_much_as_its_representative(self):
        g = self.g
        ident = self.u.formulas.index((0, 0))
        members = [i for i in np.flatnonzero(g.L0 <= 9).tolist() if F.subsumes((0, 0), self.u.formulas[i])]
        self.assertGreater(len(members), 1)
        _, alone = g.resolve(ident, "ban")
        _, whole = g.resolve(members, "ban")
        rest = np.ones(g.n, dtype=bool)
        rest[members] = False
        self.assertTrue((whole[rest] >= alone[rest]).all())
        self.assertTrue((whole[rest] > alone[rest]).any())

if __name__ == "__main__":
    unittest.main()
