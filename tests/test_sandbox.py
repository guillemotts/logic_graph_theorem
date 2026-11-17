"""The browser sandbox engine (viz/sandbox.js).

It must agree with the Python maps where they overlap, its provers must agree with its
countermodels, and the propositional map (∧, ∨, ⊥, and breakable structural rules) must be
fully settled. Runs under Node; skipped if Node or the map data is missing.
"""

import json
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NODE = shutil.which("node")
HAVE_DATA = (ROOT / "data/logics/logic_map.json").exists() and (ROOT / "data/logics/modal_map.json").exists()


def node(script: str) -> dict:
    out = subprocess.run([NODE, "-e", script], cwd=ROOT, capture_output=True, text=True, timeout=600)
    if out.returncode != 0:
        raise AssertionError(out.stderr)
    return json.loads(out.stdout)


SETUP = """
const S = require("./viz/sandbox.js"), fs = require("fs");
const load = f => JSON.parse(fs.readFileSync(f, "utf8"));
const MP = load("data/logics/modal_map.json");
const princ = m => m.principles.map(p => ({ key: p.key, name: p.name, formula: S.canon(S.parsePolish(p.polish)) }));
const CAT = S.PROP.catalog;
const title = n => n.flag || n.title;
const groupOf = (m, base) => m.nodes.findIndex(n => n.bases.some(b => b.join("+") === base.join("+")));
const cell = (m, base, k) => m.bases.find(b => b.axioms.join("+") === base.join("+")).cells[k];
const proving = c => ["given", "proved", "chained", "instance", "decided"].includes(c.status);
"""


@unittest.skipUnless(NODE and HAVE_DATA, "needs node and data/logics/*.json")
class SandboxTests(unittest.TestCase):
    def test_parity_with_python_maps(self):
        # Modal: the same map. Propositional: the old implication-and-negation map is the
        # new engine run with weakening and contraction in every base (¬p read as p → ⊥).
        out = subprocess.run([NODE, "tests/sandbox_parity.js"], cwd=ROOT, capture_output=True, text=True, timeout=600)
        report = json.loads(out.stdout)
        for name, r in report.items():
            self.assertTrue(r["same_groups"], name)
            self.assertTrue(r["same_edges"], name)
            self.assertEqual(r["n_cell_disagreements"], 0, r["cell_disagreements"])
            self.assertEqual(r["unknown_js"], 0, name)

    def test_parser(self):
        r = node(SETUP + """
        const f = s => S.show(S.parse(s));
        console.log(JSON.stringify({
          peirce: f("((a -> b) -> a) -> a"), polish: f("CCCpqpp"), box: f("[]p -> p"), dia: f("<>p -> []<>p"),
          unicode: f("¬¬p → p"), and: f("p & q -> p"), or: f("p | ~p"), bot: f("_|_ -> p"), mixed: f("~(p & ~p)"),
          polishOr: f("ApNp"), modal: S.hasBox(S.parse("□p → p")), prop: S.hasBox(S.parse("p -> p")),
          negIsImp: JSON.stringify(S.parse("~p")),
          bad: (() => { try { S.parse("p -> "); return "parsed"; } catch (e) { return "error"; } })()
        }));""")
        self.assertEqual(r["peirce"], "((p → q) → p) → p")
        self.assertEqual(r["polish"], r["peirce"])
        self.assertEqual(r["box"], "□p → p")
        self.assertEqual(r["dia"], "◇p → □◇p")
        self.assertEqual(r["unicode"], "¬¬p → p")
        self.assertEqual(r["and"], "(p ∧ q) → p")
        self.assertEqual(r["or"], "p ∨ ¬p")
        self.assertEqual(r["bot"], "⊥ → p")
        self.assertEqual(r["mixed"], "¬(p ∧ ¬p)")
        self.assertEqual(r["polishOr"], "p ∨ ¬p")
        self.assertEqual(r["negIsImp"], '["C",0,["F"]]')       # propositional ¬p is p → ⊥
        self.assertTrue(r["modal"])
        self.assertFalse(r["prop"])
        self.assertEqual(r["bad"], "error")

    def test_structural_rules_and_deciders(self):
        cases = [
            ("p -> (q -> p)", "linear", False), ("p -> (q -> p)", "affine", True), ("p -> (q -> p)", "relevant", False),
            ("(p -> (p -> q)) -> (p -> q)", "affine", False), ("(p -> (p -> q)) -> (p -> q)", "relevant", True),
            ("~(p & ~p)", "affine", False), ("~(p & ~p)", "relevant", True),              # non-contradiction needs contraction
            ("(p & (q | r)) -> ((p & q) | (p & r))", "affine", False),
            ("(p & (q | r)) -> ((p & q) | (p & r))", "relevant", False),
            ("(p & (q | r)) -> ((p & q) | (p & r))", "minimal", True),                    # distribution needs both rules
            ("(p -> q) -> (~q -> ~p)", "linear", True), ("p -> ~~p", "linear", True),
            ("~~(p | ~p)", "minimal", True), ("p | ~p", "intuitionistic", False), ("p | ~p", "classical", True),
            ("~p | ~~p", "intuitionistic", False), ("~p | ~~p", "LC", True), ("((p -> q) -> p) -> p", "LC", False),
        ]
        r = node(SETUP + f"""
        const cases = {json.dumps(cases)};
        console.log(JSON.stringify(cases.map(([s, l]) => S.isTheorem(S.parse(s), l))));""")
        for (s, logic, want), got in zip(cases, r):
            self.assertEqual(got, want, f"{s} in {logic}")

    def test_provers_agree_with_models(self):
        # Two independent methods: anything a prover proves must hold in every model of that
        # logic, and the logics must nest (linear ⊆ affine, relevant ⊆ minimal ⊆ ... ⊆ classical).
        r = node(SETUP + """
        let seed = 11; const rnd = () => (seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648;
        const gen = d => { if (d === 0 || rnd() < 0.2) return rnd() < 0.12 ? ["F"] : Math.floor(rnd() * 3);
                           const x = rnd(); return [x < 0.55 ? "C" : x < 0.78 ? "A" : "O", gen(d - 1), gen(d - 1)]; };
        const ms = S.models(S.PROP), v = Object.fromEntries(CAT.map(p => [p.key, S.validity(S.PROP, p.formula)]));
        const floors = { linear: [], affine: ["K"], relevant: ["W"], minimal: ["K", "W"], intuitionistic: ["K", "W", "EFQ"],
                         LC: ["K", "W", "EFQ", "LIN"], classical: ["K", "W", "DNE"] };
        const nest = [["linear", "affine"], ["linear", "relevant"], ["affine", "minimal"], ["relevant", "minimal"],
                      ["minimal", "intuitionistic"], ["intuitionistic", "LC"], ["LC", "classical"]];
        const bad = [], proved = {};
        for (let n = 0; n < 600; n++) {
          const t = S.canon(gen(4)), val = S.validity(S.PROP, t), r = {};
          for (const [lg, ks] of Object.entries(floors)) {
            r[lg] = S.isTheorem(t, lg);
            if (!r[lg]) continue;
            proved[lg] = (proved[lg] || 0) + 1;
            for (let i = 0; i < ms.length; i++) if (ks.every(k => v[k][i] === 1) && val[i] === 0) { bad.push(lg + ": " + S.show(t)); break; }
          }
          for (const [a, b] of nest) if (r[a] && !r[b]) bad.push(a + " not in " + b + ": " + S.show(t));
        }
        console.log(JSON.stringify({ bad, proved }));""")
        self.assertEqual(r["bad"], [])
        self.assertGreater(r["proved"]["linear"], 10)
        self.assertGreater(r["proved"]["classical"], r["proved"]["intuitionistic"])

    def test_propositional_map_is_settled(self):
        r = node(SETUP + """
        const m = S.computeMap(S.PROP, CAT, { maxCombo: 3, floorCombo: 1, extraBases: [["EFQ", "LEM"], ["K", "DNE"]] });
        const affDist = cell(m, ["K"], "DIST");
        console.log(JSON.stringify({
          unknown: m.status.unknown || 0, uncertified: m.edges.filter(e => !e.strict_by).length, n: m.nodes.length,
          titles: m.nodes.map(title),
          peirce: ["K", "W", "LEM", "EFQ"].map(k => proving(cell(m, ["PEIRCE"], k))),
          peirceNode: title(m.nodes[groupOf(m, ["PEIRCE"])]),
          lemEfqW: proving(cell(m, ["EFQ", "LEM"], "W")), lemW: proving(cell(m, ["LEM"], "W")),
          affDneEfq: proving(cell(m, ["K", "DNE"], "EFQ")), affDneW: cell(m, ["K", "DNE"], "W").status,
          relNc: proving(cell(m, ["W"], "NC")), affNc: cell(m, ["K"], "NC").status,
          affDist: [affDist.status, m.models[affDist.model].values.length],
        }));""")
        self.assertEqual(r["unknown"], 0)
        self.assertEqual(r["uncertified"], 0)
        for name in ["linear", "affine", "relevant", "minimal", "intuitionistic", "classical", "Gödel–Dummett", "Jankov",
                     "minimal + PEIRCE"]:
            self.assertIn(name, r["titles"])
        self.assertEqual(r["peirce"], [True, True, True, False])     # Peirce's law brings both structural rules, not explosion
        self.assertEqual(r["peirceNode"], "minimal + PEIRCE")
        self.assertTrue(r["lemEfqW"])                                # excluded middle + explosion give contraction...
        self.assertFalse(r["lemW"])                                  # ...excluded middle alone does not
        self.assertTrue(r["affDneEfq"])                              # with weakening, double negation gives explosion
        self.assertEqual(r["affDneW"], "refuted")
        self.assertTrue(r["relNc"])
        self.assertEqual(r["affNc"], "refuted")
        self.assertEqual(r["affDist"][0], "refuted")
        self.assertGreaterEqual(r["affDist"][1], 6)                   # needs one of the searched algebras

    def test_adding_a_known_principle_lands_in_the_right_logic(self):
        # Double negation written differently must join classical logic; excluded middle as
        # "q or not q" must join the excluded-middle logic.
        r = node(SETUP + """
        const pr = CAT.concat([
          { key: "X", name: "DNE again", formula: S.parse("~~q -> q"), custom: true },
          { key: "Y", name: "LEM again", formula: S.parse("~a | a"), custom: true }]);
        const m = S.computeMap(S.PROP, pr, { maxCombo: 1, floorCombo: 1 });
        console.log(JSON.stringify({ x: title(m.nodes[groupOf(m, ["K", "W", "X"])]), y: groupOf(m, ["Y"]) === groupOf(m, ["LEM"]),
                                     unknown: m.status.unknown || 0 }));""")
        self.assertEqual(r["x"], "classical")
        self.assertTrue(r["y"])
        self.assertEqual(r["unknown"], 0)

    def test_removing_explosion_removes_intuitionistic_logic(self):
        r = node(SETUP + """
        const m = S.computeMap(S.PROP, CAT.filter(p => p.key !== "EFQ"), { maxCombo: 2, floorCombo: 1 });
        console.log(JSON.stringify({ titles: m.nodes.map(title) }));""")
        self.assertNotIn("intuitionistic", r["titles"])
        self.assertIn("classical", r["titles"])

    def test_degenerate_logics_are_flagged(self):
        r = node(SETUP + """
        const m = S.computeMap(S.MODAL, princ(MP), { maxCombo: 2 });
        const pr = CAT.concat([{ key: "Z", name: "bad", formula: S.parse("p -> q"), custom: true }]);
        const p = S.computeMap(S.PROP, pr, { maxCombo: 1, floorCombo: 1 });
        console.log(JSON.stringify({ dl: m.nodes[groupOf(m, ["D", "L"])].flag, bl: m.nodes[groupOf(m, ["B", "L"])].flag,
                                     s5: m.nodes[groupOf(m, ["T", "5"])].flag, z: p.nodes[groupOf(p, ["Z"])].flag }));""")
        self.assertEqual(r["dl"], "inconsistent")    # Löb + seriality: no frames at all
        self.assertEqual(r["bl"], "ver")             # Löb + symmetry: every world is a dead end
        self.assertIsNone(r["s5"])
        self.assertEqual(r["z"], "inconsistent")     # a non-tautology proves everything, even in linear logic

    def test_baked_in_assumptions(self):
        r = node(SETUP + """
        const pr = princ(MP), cat = pr.map(p => p.key), out = {};
        for (const set of [["T", "5", "4"], ["T", "B", "4"], ["D", "T"], ["L", "4"], ["B", "4", "5"], ["T", "4"]]) {
          const m = S.computeMap(S.MODAL, pr, { maxCombo: 3, extraBases: S.neighbourhood(set, cat) });
          const b = S.bakedIn(m, set);
          out[set.join("+")] = Object.fromEntries(Object.entries(b).map(([k, v]) => [k, v.map(w => w.from.slice().sort().join("+"))]));
        }
        const pc = CAT.map(p => p.key), set = ["K", "W", "EFQ", "PEIRCE", "DNE"];
        const m = S.computeMap(S.PROP, CAT, { maxCombo: 1, floorCombo: 1, extraBases: S.neighbourhood(set, pc) });
        out.prop = Object.fromEntries(Object.entries(S.bakedIn(m, set)).map(([k, v]) => [k, v.map(w => w.from.slice().sort().join("+"))]));
        console.log(JSON.stringify(out));""")
        self.assertEqual(r["T+5+4"], {"T": [], "5": [], "4": ["5+T"]})             # S5: 4 follows from T + 5
        self.assertEqual(r["T+B+4"], {"T": [], "B": [], "4": []})                  # S5 again, but nothing redundant
        self.assertEqual(r["D+T"], {"D": ["T"], "T": []})
        self.assertEqual(r["L+4"], {"L": [], "4": ["L"]})                          # Löb's axiom gives 4
        self.assertEqual(r["B+4+5"], {"B": [], "4": ["5+B"], "5": ["4+B"]})       # either of 4, 5 can go, not both
        self.assertEqual(r["T+4"], {"T": [], "4": []})
        p = r["prop"]
        self.assertIn("PEIRCE", p["K"])                                            # Peirce's law gives weakening...
        self.assertIn("PEIRCE", p["W"])                                            # ...and contraction
        self.assertIn("DNE+K", p["EFQ"])                                           # weakening + double negation give explosion
        self.assertIn("EFQ+PEIRCE", p["DNE"])                                      # intuitionistic + Peirce is classical


if __name__ == "__main__":
    unittest.main()
