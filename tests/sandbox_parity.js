// Run the browser sandbox engine on the same principles and bases as the Python maps,
// and compare the results. Prints a JSON report; tests/test_sandbox.py checks it.
//
// The Python propositional map is the old implication-and-negation map on top of minimal
// logic. The sandbox reads ¬p as p → ⊥ and treats weakening (K) and contraction (W) as
// assumptions, so it is run with K and W added to every base and they are left out of the
// comparison.
const path = require("path");
const fs = require("fs");
const S = require(path.join(__dirname, "..", "viz", "sandbox.js"));

const root = path.join(__dirname, "..");
const out = {};
for (const [name, file, lang, floor] of [["propositional", "data/logics/logic_map.json", S.PROP, ["K", "W"]],
                                         ["modal", "data/logics/modal_map.json", S.MODAL, []]]) {
  const py = JSON.parse(fs.readFileSync(path.join(root, file), "utf8"));
  const principles = S.PROP.catalog.filter(p => floor.includes(p.key))
    .concat(py.principles.map(p => ({ key: p.key, name: p.name, formula: S.canon(S.parsePolish(p.polish)) })));
  const bases = py.bases.map(b => [...floor, ...b.axioms]);
  const t0 = Date.now();
  const js = S.computeMap(lang, principles, { bases, instanceBudgetMs: 2000 });
  const ms = Date.now() - t0;
  const proving = st => ["given", "proved", "chained", "instance", "decided"].includes(st);
  let cellDisagree = [], unknownJs = 0;
  py.bases.forEach((b, i) => {
    for (const k of Object.keys(b.cells)) {
      const a = b.cells[k].status, c = js.bases[i].cells[k].status;
      if (c === "unknown") unknownJs++;
      if (proving(a) !== proving(c) || (a === "refuted") !== (c === "refuted")) cellDisagree.push(`${b.name}:${k} py=${a} js=${c}`);
    }
  });
  const strip = b => b.filter(k => !floor.includes(k)).join("+");
  const nodeName = (m, n) => m.nodes[n].bases.map(b => strip(b.axioms || b)).sort().join(" = ");
  const groups = m => m.nodes.map((_, i) => nodeName(m, i)).sort();
  const edgeSet = m => m.edges.map(e => nodeName(m, e.from) + " -> " + nodeName(m, e.to)).sort();
  out[name] = {
    ms, nodes_py: py.nodes.length, nodes_js: js.nodes.length,
    same_groups: JSON.stringify(groups(py)) === JSON.stringify(groups(js)),
    same_edges: JSON.stringify(edgeSet(py)) === JSON.stringify(edgeSet(js)),
    cell_disagreements: cellDisagree.slice(0, 20), n_cell_disagreements: cellDisagree.length,
    unknown_js: unknownJs, status_js: js.status,
  };
}
console.log(JSON.stringify(out, null, 1));
