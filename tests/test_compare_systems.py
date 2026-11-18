import csv
import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from logicgraph import formula as F
from logicgraph.compare_systems import compare, ranks
from logicgraph.generate import generate


class ClaviusSystemTests(unittest.TestCase):
    """Lukasiewicz's syllogism / Clavius / Duns Scotus axioms."""

    @classmethod
    def setUpClass(cls):
        cls.ax = F.axioms("clavius")
        cls.u = generate(cls.ax, 11)

    def test_counts(self):
        expected = {1: 3, 3: 9, 5: 29, 7: 92, 9: 293, 11: 953}
        for n, total in expected.items():
            self.assertEqual(sum(1 for s in self.u.steps if s <= n), total, f"at {n} steps")

    def test_sound_and_replayable(self):
        for t, proof in zip(self.u.formulas, self.u.proof):
            self.assertTrue(F.is_tautology(t), F.to_str(t))
            self.assertEqual(F.eval_dproof(proof, self.ax), t)

    def test_identity_at_five_steps(self):
        self.assertEqual(self.u.steps[self.u.formulas.index((0, 0))], 5)

    def test_no_axiom_shared_with_lukasiewicz(self):
        self.assertFalse(set(self.ax) & set(F.axioms("lukasiewicz")))


def write_run(d: Path, axioms: str, rows: list[tuple]) -> None:
    """rows: (polish, min_steps, size, gain, knockout, affected, named)."""
    d.mkdir()
    (d / "meta.json").write_text(json.dumps({"axioms": axioms, "max_steps": 21}))
    with open(d / "theorems.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "formula", "readable", "pm", "setmm"])
        for i, r in enumerate(rows):
            w.writerow([i, r[0], r[0], "*1" if r[6] else "", ""])
    with open(d / "scores.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "min_steps", "size", "deep", "n_derivations", "n_uses", "min_uses",
                    "is_target", "is_candidate", "gain", "knockout", "lost", "affected"])
        for i, r in enumerate(rows):
            w.writerow([i, r[1], r[2], r[1] / r[2], 1, 1, 1, 1, 1, r[3], r[4], 0, r[5]])


class CompareTests(unittest.TestCase):
    def test_ranks(self):
        self.assertEqual(ranks(np.array([3, 10, 3, 1])).tolist(), [2, 1, 2, 4])

    def test_a_run_against_itself_agrees_perfectly(self):
        rng = np.random.default_rng(0)
        rows = [(f"T{i}", 3 + 2 * (i % 4), 5 + i % 7, (37 * i) % 101, (11 * i) % 53, i % 13, i % 9 == 0)
                for i in range(120)]
        with tempfile.TemporaryDirectory() as tmp:
            a, b = Path(tmp) / "a", Path(tmp) / "b"
            write_run(a, "x", rows)
            # b: same theorems, plus one only b has; reversed file order must not matter
            write_run(b, "y", rows[::-1] + [("EXTRA", 5, 5, 999, 0, 0, False)])
            res, text = compare(a, b, rng)
        self.assertEqual(res["n_shared_cands"], 120)
        self.assertAlmostEqual(res["spearman_steps"], 1.0)
        for col in ("gain", "knockout", "affected"):
            self.assertAlmostEqual(res["scores"][col]["spearman"], 1.0)
            self.assertEqual(res["scores"][col]["top20"], 20)
        self.assertAlmostEqual(res["spearman_gain_within_length"], 1.0)
        self.assertTrue(any("High in both" in line for line in text))


if __name__ == "__main__":
    unittest.main()
