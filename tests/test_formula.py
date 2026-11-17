import unittest
from pathlib import Path

from logicgraph import formula as F
from logicgraph import pmproofs

AX = F.axioms("lukasiewicz")
PM_FILE = Path(__file__).resolve().parent.parent / "data" / "raw" / "pmproofs.txt"


class FormulaTests(unittest.TestCase):
    def test_identity_proof(self):
        # The worked example in docs/NOTES.md: DD211 proves p -> p in five steps.
        self.assertEqual(F.eval_dproof("DD211", AX), (0, 0))

    def test_syllogism_proof(self):
        # pmproofs.txt *1.6: DD2D121 proves (p -> q) -> ((r -> p) -> (r -> q)).
        self.assertEqual(F.to_polish(F.eval_dproof("DD2D121", AX)), "CCpqCCrpCrq")

    def test_cd_needs_implication_and_unifier(self):
        self.assertIsNone(F.cd(0, AX[0]))                       # major is a bare variable
        self.assertIsNone(F.cd((((0,), 0), 1), (0, 0)))         # ~p -> p never matches q -> q
        # Occurs check: major (p -> (p -> q)) -> q against minor p' -> p' fails.
        self.assertIsNone(F.cd(((0, (0, 1)), 1), (0, 0)))

    def test_canonical_form(self):
        self.assertEqual(F.canon((7, (3, 7))), (0, (1, 0)))
        self.assertEqual(F.canon(((5,), 5)), ((0,), 0))

    def test_notations_round_trip(self):
        for polish in ["CpCqp", "CCpCqrCCpqCpr", "CCNpNqCqp", "NNp", "CCCpqpp"]:
            t = F.parse_polish(polish)
            self.assertEqual(F.to_polish(t), polish)
            self.assertEqual(F.canon(F.parse_infix(F.to_setmm(t))), F.canon(t))
        self.assertEqual(F.parse_infix("((~ P -> ~ Q) -> (Q -> P))"), AX[2])
        self.assertEqual(F.to_setmm(AX[0]), "( ph -> ( ps -> ph ) )")
        self.assertEqual(F.to_str(AX[2]), "(¬p → ¬q) → (q → p)")

    def test_tautology(self):
        for a in AX:
            self.assertTrue(F.is_tautology(a))
        self.assertTrue(F.is_tautology(F.parse_polish("CCCpqpp")))      # Peirce's law
        self.assertFalse(F.is_tautology(F.parse_polish("CpCpq")))

    def test_subsumes(self):
        self.assertTrue(F.subsumes((0, 0), ((1, 2), (1, 2))))
        self.assertFalse(F.subsumes(((1, 2), (1, 2)), (0, 0)))
        self.assertFalse(F.subsumes((0, 0), (0, 1)))

    def test_size(self):
        self.assertEqual(F.size(AX[0]), 5)       # p -> (q -> p): 3 variables + 2 arrows
        self.assertEqual(F.size(((0,), 0)), 4)


@unittest.skipUnless(PM_FILE.exists(), "data/raw/pmproofs.txt not downloaded")
class PrincipiaTests(unittest.TestCase):
    def test_every_published_proof_replays(self):
        entries = pmproofs.parse(PM_FILE.read_text())
        self.assertGreaterEqual(len(entries), 193)
        self.assertEqual(pmproofs.verify(entries), [])


if __name__ == "__main__":
    unittest.main()
