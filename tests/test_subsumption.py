import unittest

from logicgraph import formula as F
from logicgraph.generate import generate
from logicgraph.subsumption import GeneralizationIndex, redundant

AX = F.axioms("lukasiewicz")
P = F.parse_polish


class SubsumptionTests(unittest.TestCase):
    def test_index_finds_generalizations(self):
        index = GeneralizationIndex()
        for k, s in enumerate(["CpCqp", "Cpp", "CpCpq", "CCpqCpq"]):
            index.add(k, P(s))
        found = lambda s: sorted(k for k, _ in index.generalizations(P(s)))
        self.assertEqual(found("CpCpp"), [0, 2])         # instance of ax-1 and of p -> (p -> q)
        self.assertEqual(found("CCpqCpq"), [1, 3])       # instance of p -> p, and itself
        self.assertEqual(found("CNpNp"), [1])
        self.assertEqual(found("CpCqr"), [])

    def test_index_agrees_with_brute_force(self):
        u = generate(AX, 11)
        index = GeneralizationIndex()
        for i, t in enumerate(u.formulas):
            index.add(i, t)
        for i in range(0, len(u), 7):
            t = u.formulas[i]
            brute = sorted(j for j, g in enumerate(u.formulas) if F.subsumes(g, t))
            self.assertEqual(sorted(j for j, _ in index.generalizations(t)), brute)

    def test_redundant(self):
        u = generate(AX, 13)
        red = redundant(u.formulas, u.steps)
        by_formula = {F.to_polish(t): i for i, t in enumerate(u.formulas)}
        self.assertEqual(red[by_formula["CpCpp"]], by_formula["CpCqp"])     # instance of ax-1
        self.assertEqual(red[by_formula["CNpNp"]], by_formula["Cpp"])       # instance of p -> p
        self.assertIsNone(red[by_formula["Cpp"]])
        self.assertTrue(all(red[a] is None for a in range(u.n_axioms)))
        for i, j in enumerate(red):
            if j is not None:
                self.assertLessEqual(u.steps[j], u.steps[i])
                self.assertTrue(F.subsumes(u.formulas[j], u.formulas[i]))


if __name__ == "__main__":
    unittest.main()
