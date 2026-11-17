import random
import unittest

import numpy as np

from logicgraph import formula as F
from logicgraph.generate import generate
from logicgraph.intuitionistic import is_theorem, weakest_logic
from logicgraph.matrices import (K, S, evaluate_batch, failing_assignment, heyting_models, holds, mp_closed,
                                 small_models, validity_table)
from logicgraph.principles import BASE, CATALOG

P = F.parse_polish


def random_formula(rng: random.Random, depth: int, n_vars: int = 3):
    if depth == 0 or rng.random() < 0.25:
        return rng.randrange(n_vars)
    if rng.random() < 0.25:
        return (random_formula(rng, depth - 1, n_vars),)
    return (random_formula(rng, depth - 1, n_vars), random_formula(rng, depth - 1, n_vars))


class DecisionTests(unittest.TestCase):
    def test_known_classification(self):
        expected = {
            "CpCqp": "minimal", "CCpCqrCCpqCpr": "minimal", "CCpqCCpNqNp": "minimal", "CpNNp": "minimal",
            "CCpqCNqNp": "minimal", "CNNNpNp": "minimal", "CNpCpNq": "minimal",
            "CNpCpq": "intuitionistic", "NNCNNpp": "intuitionistic",
            "CNNpp": "classical", "CCCpqpp": "classical", "CCNppp": "classical", "CCNpNqCqp": "classical",
            "CpCpq": "none",
        }
        for polish, logic in expected.items():
            self.assertEqual(weakest_logic(P(polish)), logic, polish)

    def test_ladder_is_nested_on_random_formulas(self):
        rng = random.Random(0)
        for _ in range(400):
            t = F.canon(random_formula(rng, 5))
            m, i, c = (is_theorem(t, l) for l in ("minimal", "intuitionistic", "classical"))
            self.assertTrue(not m or i, F.to_str(t))
            self.assertTrue(not i or c, F.to_str(t))

    def test_agrees_with_heyting_models(self):
        # Intuitionistic theorems hold in every Heyting algebra with ⊥ = bottom; minimal ones for every ⊥.
        models = [m for m in heyting_models(3)]
        rng = random.Random(1)
        checked = 0
        for _ in range(600):
            t = F.canon(random_formula(rng, 5))
            for logic in ("minimal", "intuitionistic"):
                if not is_theorem(t, logic):
                    continue
                checked += 1
                for m in models:
                    if logic == "intuitionistic" and m.neg.tolist() != m.imp[:, 0].tolist():
                        continue
                    self.assertTrue(holds(t, m), f"{F.to_str(t)} fails in {m.name}")
        self.assertGreater(checked, 50)

    def test_generated_classical_theorems_are_tautologies_and_tagged(self):
        u = generate(F.axioms("lukasiewicz"), 11)
        tags = [weakest_logic(t) for t in u.formulas]
        self.assertNotIn("none", tags)
        self.assertEqual(tags[0], "minimal")            # ax-1
        self.assertEqual(tags[2], "classical")          # ax-3


class ModelTests(unittest.TestCase):
    def test_heyting_models_are_models_of_minimal_logic(self):
        red = P("CCpqCCpNqNp")
        for m in heyting_models(3):
            self.assertTrue(mp_closed(m) and holds(K, m) and holds(S, m) and holds(red, m), m.name)

    def test_godel_three_valued(self):
        g3 = next(m for m in heyting_models(2) if m.name == "Heyting(3), ⊥=0")
        self.assertFalse(holds(P("CNNpp"), g3))
        self.assertFalse(holds(P("CCCpqpp"), g3))
        self.assertTrue(holds(P("CNpCpq"), g3))
        self.assertEqual(failing_assignment(P("CNNpp"), g3), {"p": "a1"})

    def test_small_models_filter(self):
        models = small_models(3)
        self.assertGreater(len(models), 1000)
        for m in models[::97]:
            self.assertTrue(mp_closed(m) and holds(K, m) and holds(S, m))

    def test_validity_table_matches_holds(self):
        models = heyting_models(2) + small_models(2)
        formulas = [p.formula for p in BASE + CATALOG]
        table = validity_table(formulas, models)
        for i, m in enumerate(models):
            for j, t in enumerate(formulas):
                self.assertEqual(table[i, j], holds(t, m))

    def test_countermodels_never_refute_theorems(self):
        # Soundness: a principle that is a theorem of a logic holds in every model of that logic.
        models = heyting_models(3) + small_models(3)
        red = P("CCpqCCpNqNp")
        table = validity_table([red] + [p.formula for p in CATALOG], models)
        minimal_models = table[:, 0]
        for j, p in enumerate(CATALOG, start=1):
            if is_theorem(p.formula, "minimal"):
                self.assertTrue(table[minimal_models, j].all(), p.key)


class MapLogicTests(unittest.TestCase):
    """Chaining and node building on a hand-made example (no search involved)."""

    def cells(self):
        from copy import deepcopy
        g = lambda: {"status": "given"}
        pr = lambda: {"status": "proved"}
        rf = lambda: {"status": "refuted", "model": 0}
        un = lambda: {"status": "unknown"}
        # Base logics: nothing, +A, +B, +C. A proves B; B proves C; C proves nothing new.
        return deepcopy({
            (): {"A": rf(), "B": rf(), "C": rf()},
            ("A",): {"A": g(), "B": pr(), "C": un()},
            ("B",): {"A": un(), "B": g(), "C": pr()},
            ("C",): {"A": rf(), "B": rf(), "C": g()},
        })

    def test_chaining_is_transitive(self):
        from logicgraph.logicmap import chain
        cells = self.cells()
        n = chain(list(cells), cells, ["A", "B", "C"])
        self.assertEqual(n, 1)
        self.assertEqual(cells[("A",)]["C"]["status"], "chained")
        self.assertEqual(cells[("A",)]["C"]["via"], ["B"])

    def test_chaining_detects_contradictions(self):
        from logicgraph.logicmap import chain
        cells = self.cells()
        cells[("A",)]["C"] = {"status": "refuted", "model": 0}
        with self.assertRaises(AssertionError):
            chain(list(cells), cells, ["A", "B", "C"])

    def test_nodes_merge_equivalent_bases_and_order_the_rest(self):
        from logicgraph.logicmap import build_nodes, chain
        cells = self.cells()
        cells[("B",)]["A"] = {"status": "proved"}           # now A and B are equivalent
        chain(list(cells), cells, ["A", "B", "C"])
        nodes, edges = build_nodes(list(cells), cells, ["A", "B", "C"])
        groups = sorted(sorted(n["bases"]) for n in nodes)
        self.assertEqual(groups, [[()], [("A",), ("B",)], [("C",)]])
        names = {i: tuple(n["rep"]) for i, n in enumerate(nodes)}
        pairs = {(names[e["from"]], names[e["to"]]) for e in edges}
        self.assertEqual(pairs, {((), ("C",)), (("C",), ("A",))})   # covering edges only
        for e in edges:
            self.assertIsNotNone(e["strict_by"])


class InstanceTests(unittest.TestCase):
    def formulas(self):
        return {p.key: p.formula for p in CATALOG}

    def test_peirce_gives_consequentia_mirabilis_over_minimal(self):
        from logicgraph.logicmap import derive_by_instances
        f = {k: v for k, v in self.formulas().items() if k in ("PEIRCE", "CM", "TNE")}
        cells = {("PEIRCE",): {"PEIRCE": {"status": "given"}, "CM": {"status": "unknown"},
                               "TNE": {"status": "refuted", "model": 0}}}
        derive_by_instances(list(cells), cells, f)
        c = cells[("PEIRCE",)]
        self.assertEqual(c["CM"]["status"], "instance")
        self.assertEqual(c["CM"]["by"], "minimal")
        self.assertEqual(c["TNE"]["status"], "refuted")          # settled cells are left alone

    def test_instance_certificates_are_theorems(self):
        from logicgraph.logicmap import derive_by_instances, instances, _pool
        f = {k: v for k, v in self.formulas().items() if k in ("EFQ", "PEIRCE", "DNE")}
        cells = {("EFQ", "PEIRCE"): {"EFQ": {"status": "given"}, "PEIRCE": {"status": "given"},
                                     "DNE": {"status": "unknown"}}}
        derive_by_instances(list(cells), cells, f)
        c = cells[("EFQ", "PEIRCE")]
        self.assertEqual(c["DNE"]["status"], "instance")          # intuitionistic + Peirce is classical
        inst = c["DNE"]["instances"][0]["formula"]
        found = [i for i in instances(f["PEIRCE"], _pool(f["DNE"])) if F.to_str(i) == inst]
        self.assertTrue(found)
        self.assertTrue(is_theorem((found[0], f["DNE"]), "intuitionistic"))
        self.assertFalse(is_theorem(f["DNE"], "intuitionistic"))


if __name__ == "__main__":
    unittest.main()
