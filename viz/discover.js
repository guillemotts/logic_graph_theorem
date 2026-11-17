/* Discover: search for formulas that do something unexpected when added as an assumption.
 *
 * For every small classically valid formula φ that the starting logic F does not already
 * prove, add φ to F and ask the engine (sandbox.js) two questions:
 *
 *   1. Which of the named principles (weakening, contraction, explosion, …) does F + φ prove?
 *      Call that set P (its "profile").
 *   2. Does F + P prove φ back?
 *        yes → φ is a single formula that does the work of all of P. When P contains a
 *              structural rule φ does not obviously state, φ "smuggles it in" (a collapse).
 *        no  → F + φ is a logic that is not on the map: it proves exactly the principles P
 *              from the list, yet it is strictly stronger than F + P (a gap).
 *
 * Every answer is certified the same way the map is: proofs by the decision procedures or
 * substitution instances, refutations by a finite countermodel. Formulas where the engine
 * cannot settle a question within its budget are counted but not reported.
 *
 * Works in the browser (window.Discover) and in Node (module.exports).
 */
(function (root) {
  "use strict";
  const S = root.Sandbox || (typeof require !== "undefined" && require("./sandbox.js"));
  const PROVING = ["given", "proved", "chained", "instance", "decided"];

  const F = ["F"];
  const sortPair = (op, a, b) => {
    // ∧ and ∨ are commutative in every logic here, so keep one order.
    if (op !== "C" && S.key(a) > S.key(b)) [a, b] = [b, a];
    return [op, a, b];
  };

  /** Size = number of symbols (letters, ⊥, connectives). */
  function size(t) { return typeof t === "number" || t.length === 1 ? 1 : 1 + size(t[1]) + size(t[2]); }

  /** All formulas over `nVars` letters with →, ∧, ∨, ¬ (¬a is a → ⊥) and at most `maxOps`
   * connectives, up to renaming letters and swapping the sides of ∧ / ∨. ⊥ appears only
   * inside ¬, so the search stays in the familiar language of the named principles. */
  function enumerate(nVars = 2, maxOps = 3) {
    const byOps = [[...Array(nVars).keys()]];
    for (let n = 1; n <= maxOps; n++) {
      const out = byOps[n - 1].map(a => ["C", a, F]);
      for (let i = 0; i < n; i++) for (const a of byOps[i]) for (const b of byOps[n - 1 - i])
        for (const op of ["C", "A", "O"]) out.push(sortPair(op, a, b));
      byOps.push(out);
    }
    const seen = new Set(), all = [];
    for (const level of byOps) for (const t of level) {
      const c = S.canon(t), k = S.key(c);
      if (!seen.has(k)) { seen.add(k); all.push(c); }
    }
    return all;
  }

  // Starting logics: which structural principles (and explosion) they assume.
  const FLOORS = {
    linear: [], affine: ["K"], relevant: ["W"], minimal: ["K", "W"], intuitionistic: ["K", "W", "EFQ"],
  };
  const FLOOR_NAMES = { "": "linear", K: "affine", W: "relevant", "K+W": "minimal", "K+W+EFQ": "intuitionistic" };

  /** Named principles the starting logic already proves (so adding φ doesn't "gain" them). */
  const FLOOR_PROVES = {};
  function floorProves(floor) {
    if (!FLOOR_PROVES[floor]) FLOOR_PROVES[floor] = S.PROP.catalog.filter(p => S.isTheorem(p.formula, floor)).map(p => p.key);
    return FLOOR_PROVES[floor];
  }

  /** Examine one formula over a starting logic. Returns an outcome object, or null if the
   * formula is not a candidate (not classically valid, or already provable). */
  function examine(phi, floor = "linear", opts = {}) {
    // Cap each proof search so one hard sequent can't stall the run (it then counts as unsettled).
    S.setStepLimit(opts.stepLimit ?? 200000);
    try { return examineInner(phi, floor, opts); } finally { S.setStepLimit(Infinity); }
  }
  function examineInner(phi, floor, opts) {
    const lang = S.PROP, catalog = lang.catalog;
    if (!S.tautology(phi) || S.isTheorem(phi, floor)) return null;
    const base = FLOORS[floor];
    // A formula that is literally one of the named principles is no discovery.
    const named = catalog.find(p => S.key(S.canon(p.formula)) === S.key(phi))?.key || null;
    if (named) return { formula: S.show(phi), size: size(phi), floor, outcome: "named", named };
    const X = { key: "X", name: "φ", formula: phi, custom: true };
    const principles = [...catalog, X];
    const budget = { instanceBudgetMs: opts.instanceBudgetMs ?? 120, totalBudgetMs: opts.totalBudgetMs ?? 3000 };
    // Bases with the structural rules (and explosion) added let proofs found in the stronger
    // systems chain back down once F + φ is shown to prove those rules.
    const extras = [[], ["K"], ["W"], ["K", "W"], ["K", "W", "EFQ"]].map(e => [...new Set([...base, ...e, "X"])]);
    let m1;
    try { m1 = S.computeMap(lang, principles, { bases: extras, ...budget }); }
    catch (e) { return { formula: S.show(phi), size: size(phi), floor, outcome: "unsettled", unknown: ["error: " + e.message] }; }
    const c = m1.bases[0].cells;
    const P = catalog.map(p => p.key).filter(k => PROVING.includes(c[k].status));
    const unknown = catalog.map(p => p.key).filter(k => c[k].status === "unknown");
    if (unknown.length) return { formula: S.show(phi), size: size(phi), floor, outcome: "unsettled", unknown };
    // Does F + P prove φ back?
    const m2 = S.computeMap(lang, principles, { bases: [[...new Set([...base, ...P])]], ...budget });
    const back = m2.bases[0].cells.X;
    if (back.status === "unknown") return { formula: S.show(phi), size: size(phi), floor, outcome: "unsettled", unknown: ["back"] };
    const gained = P.filter(k => !base.includes(k) && !floorProves(floor).includes(k));
    const profileName = lang.describe([...new Set([...base, ...P])], k => k);
    const out = { formula: S.show(phi), size: size(phi), floor, gained, profile: profileName, tree: phi, named: null };
    if (PROVING.includes(back.status)) {
      out.outcome = "equivalent";
      // Collapse: φ brings in a structural rule (or explosion) the starting logic lacked.
      out.collapse = gained.filter(k => ["K", "W", "EFQ"].includes(k));
      // How each gained principle was obtained (the first certificate).
      out.how = Object.fromEntries(gained.map(k => [k, c[k].status === "instance" ? c[k].instances.map(i => i.formula) : c[k].status]));
    } else {
      out.outcome = "new";
      const model = m2.models[back.model];
      out.witness = { model: model.name, values: model.values, falsified_by: back.falsified_by };
      out.refutes = catalog.map(p => p.key).filter(k => c[k].status === "refuted");
    }
    return out;
  }

  /** Run a search. Returns { floor, examined, skipped, unsettled, findings } where findings
   * keeps, for each distinct result, the shortest formulas that produce it. */
  function search(opts = {}) {
    const floor = opts.floor || "linear";
    const cands = enumerate(opts.vars ?? 2, opts.maxOps ?? 3)
      .filter(t => S.tautology(t) && !S.isTheorem(t, floor))
      .sort((a, b) => size(a) - size(b) || S.key(a).localeCompare(S.key(b)));
    // Formulas that hold in exactly the same finite models usually axiomatize the same logic;
    // examine the shortest of each such class (the rest are counted, not examined).
    const classes = new Map();
    for (const t of cands) {
      const v = S.validity(S.PROP, t).join("");
      if (!classes.has(v)) classes.set(v, { rep: t, count: 0 });
      classes.get(v).count++;
    }
    const results = [];
    let examined = 0, unsettled = 0;
    const reps = [...classes.values()].slice(0, opts.limit ?? Infinity);
    for (const { rep, count } of reps) {
      const r = examine(rep, floor, opts);
      examined++;
      if (opts.onProgress) opts.onProgress(examined, reps.length);
      if (!r) continue;
      if (r.outcome === "unsettled") { unsettled++; continue; }
      if (r.outcome === "named") continue;
      r.similar = count - 1;
      results.push(r);
    }
    const findings = group(results, floor, opts.perGroup ?? 3);
    return { floor, vars: opts.vars ?? 2, maxOps: opts.maxOps ?? 3, candidates: cands.length, classes: classes.size, examined, unsettled, findings };
  }

  /* Group results by outcome and by the principles gained. An "equivalent" group is one logic
   * (every member is equivalent to F + P). A "new" group collects logics strictly above F + P,
   * which may differ from one another; only the shortest few are kept as examples. Takes plain
   * results, or saved findings (whose examples carry their own counts), so old runs can be
   * regrouped without searching again. */
  function group(results, floor, perGroup = 3) {
    const groups = new Map();
    const known = new Set([...FLOORS[floor], ...floorProves(floor)]);
    for (const r of results) {
      const gained = r.gained.filter(k => !known.has(k));
      // Equivalent with nothing gained: φ was a theorem of F after all (F's own test is bounded).
      if (r.outcome === "equivalent" && !gained.length) continue;
      const collapse = r.outcome === "equivalent" ? gained.filter(k => ["K", "W", "EFQ"].includes(k)) : [];
      const gk = r.outcome + "|" + gained.join("+");
      if (!groups.has(gk)) groups.set(gk, { outcome: r.outcome, gained, profile: S.PROP.describe([...FLOORS[floor], ...gained], k => k), collapse, examples: [], count: 0 });
      const g = groups.get(gk);
      g.count += r.groupCount ?? 1;
      const { tree, groupCount, ...ex } = r;
      g.examples.push({ ...ex, gained, collapse });
    }
    const findings = [...groups.values()];
    for (const f of findings) f.examples = f.examples.sort((a, b) => a.size - b.size || a.formula.localeCompare(b.formula)).slice(0, perGroup);
    findings.sort((a, b) => (a.outcome === "new") - (b.outcome === "new") || b.collapse.length - a.collapse.length
                             || a.examples[0].size - b.examples[0].size);
    return findings;
  }
  /** Regroup a saved run (e.g. after a change to how gains are counted). */
  function regroup(run) {
    const flat = [];
    for (const f of run.findings) f.examples.forEach((e, i) => flat.push({ ...e, outcome: f.outcome, groupCount: i === 0 ? f.count - f.examples.length + 1 : 1 }));
    return { ...run, findings: group(flat, run.floor) };
  }

  const api = { enumerate, examine, search, group, regroup, floorProves, size, FLOORS, FLOOR_NAMES };
  root.Discover = api;
  if (typeof module !== "undefined" && module.exports) module.exports = api;
})(typeof window !== "undefined" ? window : globalThis);
