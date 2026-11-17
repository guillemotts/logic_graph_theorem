"""The formula search (viz/discover.js): add one small formula to a starting logic and certify
what it brings in. Runs under Node; skipped if Node is missing."""

import json
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NODE = shutil.which("node")


def node(script: str) -> dict:
    out = subprocess.run([NODE, "-e", script], cwd=ROOT, capture_output=True, text=True, timeout=600)
    if out.returncode != 0:
        raise AssertionError(out.stderr)
    return json.loads(out.stdout)


SETUP = 'const S = require("./viz/sandbox.js"), D = require("./viz/discover.js");\n'


@unittest.skipUnless(NODE, "needs node")
class DiscoverTests(unittest.TestCase):
    def test_enumeration(self):
        r = node(SETUP + """
const all = D.enumerate(2, 3), keys = all.map(t => S.key(t));
const botOk = t => typeof t === "number" || (t[0] === "F" ? false : t.slice(1).every((x, i) => (t[0] === "C" && i === 1 && x[0] === "F") || botOk(x)));
console.log(JSON.stringify({ n: all.length, unique: new Set(keys).size, canon: all.every(t => S.key(S.canon(t)) === S.key(t)),
  bot: all.every(botOk), peirce: keys.includes(S.key(S.canon(S.parse("((p -> q) -> p) -> p")))) }));
""")
        self.assertEqual(r["n"], r["unique"])
        self.assertTrue(r["canon"] and r["bot"] and r["peirce"])

    def test_known_results_over_linear_logic(self):
        r = node(SETUP + """
const ex = src => { const x = D.examine(S.canon(S.parse(src)), "linear"); return x && { o: x.outcome, g: x.gained, c: x.collapse, named: x.named }; };
console.log(JSON.stringify({
  mp: ex("(p & (p -> q)) -> q"),          // modus ponens as a formula: contraction
  ds: ex("p -> ((q | ~p) -> q)"),         // disjunctive syllogism: weakening and explosion
  mingle: ex("p -> (p -> p)"),            // the mingle axiom: none of the named principles
  pq: ex("p | (p -> q)"),
  peirce: ex("((p -> q) -> p) -> p"),
  k: ex("(p & q) -> p"),                  // a linear theorem: not a candidate
  bad: ex("p -> q"),                      // not classically valid: not a candidate
}));
""")
        self.assertEqual(r["mp"], {"o": "equivalent", "g": ["W", "NC"], "c": ["W"], "named": None})
        self.assertEqual(r["ds"]["o"], "equivalent")
        self.assertEqual(r["ds"]["g"], ["K", "EFQ"])
        self.assertEqual(r["mingle"]["o"], "new")
        self.assertEqual(r["mingle"]["g"], [])
        self.assertEqual(r["pq"]["o"], "new")
        self.assertEqual(r["pq"]["g"], ["W", "LEM", "WLEM", "NC"])
        self.assertEqual(r["peirce"]["named"], "PEIRCE")
        self.assertIsNone(r["k"])
        self.assertIsNone(r["bad"])

    def test_saved_results_are_well_formed(self):
        path = ROOT / "data/discoveries.json"
        if not path.exists():
            self.skipTest("run scripts/discover.js first")
        d = json.loads(path.read_text())
        self.assertEqual({r["floor"] for r in d["runs"]}, {"linear", "affine", "relevant", "minimal", "intuitionistic"})
        for run in d["runs"]:
            for f in run["findings"]:
                self.assertIn(f["outcome"], ("equivalent", "new"))
                for e in f["examples"]:
                    self.assertIsNone(e["named"])
                    if f["outcome"] == "new":
                        self.assertIn("witness", e)


if __name__ == "__main__":
    unittest.main()
