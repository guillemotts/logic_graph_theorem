import random
import unittest

import numpy as np

from logicgraph import formula as F
from logicgraph.intuitionistic import is_theorem
from logicgraph.modal import (box, dia, frame_validity, frames, godel_translation, imp, is_valid, neg,
                              parse_polish, s5_valid_small, substitute)

P = parse_polish


def random_modal(rng: random.Random, d: int, k: int = 2):
    if d == 0 or rng.random() < 0.2:
        return rng.randrange(k)
    r = rng.random()
    if r < 0.25:
        return neg(random_modal(rng, d - 1, k))
    if r < 0.5:
        return box(random_modal(rng, d - 1, k))
    return imp(random_modal(rng, d - 1, k), random_modal(rng, d - 1, k))


def random_prop(rng: random.Random, d: int, k: int = 3):
    if d == 0 or rng.random() < 0.25:
        return rng.randrange(k)
    if rng.random() < 0.25:
        return (random_prop(rng, d - 1, k),)
    return (random_prop(rng, d - 1, k), random_prop(rng, d - 1, k))


class ProverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.frames = frames(3)
        r = cls.frames
        cls.refl_trans = [i for i, m in enumerate(r)
                          if m.diagonal().all() and ((m.astype(int) @ m.astype(int)) > 0).astype(bool).__le__(m).all()]

    def test_known_principles(self):
        for f, logic, expected in [("CLCpqCLpLq", "K", True), ("CLpp", "K", False), ("CLpp", "S4", True),
                                   ("CLpLLp", "S4", True), ("CMpLMp", "S4", False), ("CpLMp", "S4", False),
                                   ("CLpMp", "K", False), ("LCpp", "K", True)]:
            self.assertEqual(is_valid(P(f), logic), expected, f"{f} in {logic}")

    def test_k_theorems_hold_on_every_small_frame(self):
        rng = random.Random(0)
        formulas, valid = [], []
        while len(formulas) < 300:
            t = random_modal(rng, 4)
            formulas.append(t)
            valid.append(is_valid(t, "K"))
        table = frame_validity(formulas, self.frames)
        for j, t in enumerate(formulas):
            if valid[j]:
                self.assertTrue(table[:, j].all(), t)
        self.assertGreater(sum(valid), 10)
        # Conversely, anything refuted on a small frame must be reported invalid.
        for j in range(len(formulas)):
            if not table[:, j].all():
                self.assertFalse(valid[j])

    def test_s4_theorems_hold_on_reflexive_transitive_frames(self):
        rng = random.Random(1)
        formulas = [random_modal(rng, 4) for _ in range(300)]
        valid = [is_valid(t, "S4") for t in formulas]
        table = frame_validity(formulas, [self.frames[i] for i in self.refl_trans])
        for j in range(len(formulas)):
            if valid[j]:
                self.assertTrue(table[:, j].all(), formulas[j])
            if not table[:, j].all():
                self.assertFalse(valid[j])
        self.assertGreater(sum(valid), 20)

    def test_godel_translation_matches_intuitionistic_prover(self):
        # Two independent decision procedures (G4ip and the S4 tableau) must agree.
        rng = random.Random(2)
        n_int = 0
        for _ in range(400):
            t = F.canon(random_prop(rng, 4))
            a = is_theorem(t, "intuitionistic")
            b = is_valid(godel_translation(t), "S4")
            self.assertEqual(a, b, F.to_str(t))
            n_int += a
        self.assertGreater(n_int, 20)

    def test_godel_translation_into_s5_is_classical(self):
        rng = random.Random(3)
        for _ in range(150):
            t = F.canon(random_prop(rng, 4, k=3))
            self.assertEqual(s5_valid_small(godel_translation(t)), F.is_tautology(t), F.to_str(t))

    def test_instances_give_d_from_t(self):
        t = P("CLpp")
        d = P("CLpMp")
        self.assertTrue(is_valid(imp(t, imp(substitute(t, {0: neg(0)}), d)), "K"))
        self.assertFalse(is_valid(imp(t, d), "K"))


if __name__ == "__main__":
    unittest.main()


class ModalMapTests(unittest.TestCase):
    """The modal cube is a textbook result; the map must reproduce it with certificates."""

    @classmethod
    def setUpClass(cls):
        from logicgraph.logicmap import build_nodes, chain
        from logicgraph.modalmap import CUBE, ModalMapBuilder, bases
        b = ModalMapBuilder(4, lambda *a: None)
        cube = [x for x in bases() if set(x) <= set(CUBE)]
        cells = {x: b.refute(x) for x in cube}
        while True:
            changed = b.decide(cube, cells) + chain(cube, cells, b.keys)
            if not changed:
                for x in sorted(cube, key=len):
                    for k in b.keys:
                        if cells[x][k]["status"] == "unknown" and k in CUBE:
                            hit = b.by_instances(x, k)
                            if hit:
                                cells[x][k] = hit
                                changed += 1
                                break
                    if changed:
                        break
            if not changed:
                break
        keys = list(CUBE)
        cls.cells = cells
        cls.nodes, cls.edges = build_nodes(cube, {x: {k: cells[x][k] for k in keys} for x in cube}, keys)

    def test_fifteen_logics(self):
        self.assertEqual(len(self.nodes), 15)

    def test_known_identifications(self):
        group = {tuple(sorted(x)): i for i, n in enumerate(self.nodes) for x in n["bases"]}
        same = lambda *xs: len({group[tuple(sorted(x))] for x in xs}) == 1
        self.assertTrue(same(("T", "5"), ("T", "B", "4"), ("D", "B", "4"), ("T", "4", "5")))   # S5
        self.assertTrue(same(("B", "4"), ("B", "5")))
        self.assertTrue(same(("T",), ("D", "T")))
        self.assertFalse(same(("T", "4"), ("T", "5")))                                       # S4 is not S5
        self.assertFalse(same(("D", "4", "5"), ("T", "4", "5")))                             # KD45 is not S5

    def test_every_cube_cell_is_settled_and_every_edge_certified(self):
        for x, c in self.cells.items():
            for k in ("D", "T", "B", "4", "5"):
                self.assertNotEqual(c[k]["status"], "unknown", (x, k))
        for e in self.edges:
            self.assertIsNotNone(e["strict_by"])
