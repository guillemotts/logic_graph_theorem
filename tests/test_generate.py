import unittest
from pathlib import Path

from logicgraph import formula as F
from logicgraph import pmproofs
from logicgraph.generate import generate

AX = F.axioms("lukasiewicz")
PM_FILE = Path(__file__).resolve().parent.parent / "data" / "raw" / "pmproofs.txt"


class GenerateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.u = generate(AX, 15)

    def test_counts_per_horizon(self):
        # Cumulative number of distinct theorems provable in <= n steps.
        expected = {1: 3, 3: 9, 5: 24, 7: 74, 9: 213, 11: 648, 13: 2068, 15: 6563}
        for n, total in expected.items():
            self.assertEqual(sum(1 for s in self.u.steps if s <= n), total, f"at {n} steps")

    def test_every_theorem_is_a_tautology(self):
        for t in self.u.formulas:
            self.assertTrue(F.is_tautology(t), F.to_str(t))

    def test_stored_proofs_replay(self):
        for t, proof, steps in zip(self.u.formulas, self.u.proof, self.u.steps):
            self.assertEqual(len(proof), steps)
            self.assertEqual(F.eval_dproof(proof, AX), t)

    def test_identity_found_at_five_steps(self):
        i = self.u.formulas.index((0, 0))
        self.assertEqual(self.u.steps[i], 5)
        self.assertEqual(self.u.proof[i], "DD211")

    def test_derivations_respect_horizon_and_are_sound(self):
        seen = set()
        for c, a, b in self.u.derivations:
            self.assertLessEqual(self.u.steps[a] + self.u.steps[b] + 1, self.u.max_steps)
            self.assertGreaterEqual(self.u.steps[a] + self.u.steps[b] + 1, self.u.steps[c])
            self.assertNotIn((a, b), seen)
            seen.add((a, b))
        for c, a, b in self.u.derivations[:3000]:
            self.assertEqual(F.cd(self.u.formulas[a], self.u.formulas[b]), self.u.formulas[c])

    def test_every_non_axiom_has_a_shortest_derivation(self):
        best = {}
        for c, a, b in self.u.derivations:
            n = self.u.steps[a] + self.u.steps[b] + 1
            best[c] = min(best.get(c, n), n)
        for i in range(self.u.n_axioms, len(self.u)):
            self.assertEqual(best[i], self.u.steps[i])

    @unittest.skipUnless(PM_FILE.exists(), "data/raw/pmproofs.txt not downloaded")
    def test_agrees_with_published_shortest_proofs(self):
        # Published proofs of <= 21 steps are known to be shortest; ours must match.
        steps = dict(zip(self.u.formulas, self.u.steps))
        checked = 0
        for e in pmproofs.parse(PM_FILE.read_text()):
            if e.steps <= self.u.max_steps:
                self.assertEqual(steps.get(e.result), e.steps, e.number)
                checked += 1
            else:
                self.assertNotIn(e.result, steps, f"{e.number} found with a shorter proof than published")
        self.assertGreater(checked, 10)


if __name__ == "__main__":
    unittest.main()
