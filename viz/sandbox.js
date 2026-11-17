/* Logic sandbox engine: add or remove assumptions and recompute the map of logics.
 *
 * Runs in the page and in Node (tests/test_sandbox.py checks it, including against the
 * Python maps).
 *
 * Formulas: a variable is a number 0, 1, ...; ["C", a, b] is a → b; ["L", a] is □a.
 *   Propositional formulas also use ["A", a, b] (a ∧ b), ["O", a, b] (a ∨ b) and ["F"] (⊥);
 *   ¬a is a → ⊥.
 *   Modal formulas use ["N", a] for ¬a and the classical encodings of ∧ and ∨; ◇a = ¬□¬a.
 *
 * The propositional map starts from a core that every logic on it keeps: hypotheses can be
 * used in any order (exchange), implications chain (composition), p → p, and ∧ / ∨ behave as
 * "both" and "either". That core is the →∧∨ part of intuitionistic linear logic. Two
 * structural rules are ordinary, breakable assumptions on top of it:
 *   K  weakening    p → (q → p)              an unused hypothesis does no harm
 *   W  contraction  (p → (p → q)) → (p → q)  a hypothesis can be used twice
 * Core + K is affine logic, core + W relevant logic (without distribution), core + K + W is
 * minimal logic, and explosion (⊥ → p) on top of that gives intuitionistic logic.
 *
 * For a base logic B (the core plus some principles) and a principle P, a cell gets one of:
 *   given / refuted (countermodel) / instance / decided / chained / unknown
 */
(function (root) {
  "use strict";

  // ------------------------------------------------------------ formulas
  const N = a => ["N", a], C = (a, b) => ["C", a, b], L = a => ["L", a];
  const F = ["F"], A = (a, b) => ["A", a, b], O = (a, b) => ["O", a, b];
  const NOT = a => C(a, F);
  const M = a => N(L(N(a)));
  // Classical encodings, used for modal formulas.
  const AND = (a, b) => N(C(a, N(b)));
  const OR = (a, b) => C(N(a), b);
  const LETTERS = "pqrstuvw";

  function key(t) {
    if (typeof t === "number") return "#" + t + ".";
    return t[0] + t.slice(1).map(key).join("");
  }
  function vars(t, out = new Set()) {
    if (typeof t === "number") out.add(t); else for (let i = 1; i < t.length; i++) vars(t[i], out);
    return out;
  }
  function nvars(t) { const v = vars(t); return v.size ? Math.max(...v) + 1 : 0; }
  function hasBox(t) { return typeof t !== "number" && (t[0] === "L" || t.slice(1).some(hasBox)); }
  function mdepth(t) {
    if (typeof t === "number" || t.length === 1) return 0;
    const d = Math.max(...t.slice(1).map(mdepth));
    return t[0] === "L" ? d + 1 : d;
  }
  function subst(t, s) { return typeof t === "number" ? (t in s ? s[t] : t) : [t[0], ...t.slice(1).map(x => subst(x, s))]; }
  function canon(t) {
    const m = new Map();
    const go = x => typeof x === "number" ? (m.has(x) || m.set(x, m.size), m.get(x)) : [x[0], ...x.slice(1).map(go)];
    return go(t);
  }
  const isBot = t => typeof t !== "number" && t[0] === "F";
  function show(t, top = true) {
    if (typeof t === "number") return LETTERS[t] || "v" + t;
    const wrap = s => top ? s : "(" + s + ")";
    switch (t[0]) {
      case "F": return "⊥";
      case "L": return "□" + show(t[1], false);
      case "A": return wrap(show(t[1], false) + " ∧ " + show(t[2], false));
      case "O": return wrap(show(t[1], false) + " ∨ " + show(t[2], false));
      case "N": {
        const a = t[1];
        if (typeof a !== "number" && a[0] === "L" && typeof a[1] !== "number" && a[1][0] === "N") return "◇" + show(a[1][1], false);
        if (typeof a !== "number" && a[0] === "C" && typeof a[2] !== "number" && a[2][0] === "N") return wrap(show(a[1], false) + " ∧ " + show(a[2][1], false));
        return "¬" + show(a, false);
      }
      default:
        if (isBot(t[2])) return "¬" + show(t[1], false);
        return wrap(show(t[1], false) + " → " + show(t[2], false));
    }
  }

  // The parsers build a neutral tree (N, C, A, O, F, L); `normalize` then picks the
  // encoding: modal formulas (anything with □ or ◇) keep ¬ and encode ∧ / ∨ classically,
  // propositional ones keep ∧ / ∨ and read ¬a as a → ⊥.
  function normalize(t) {
    const modal = hasBox(t);
    const go = x => {
      if (typeof x === "number" || x[0] === "F") return x;
      const [a, b] = [go(x[1]), x.length > 2 ? go(x[2]) : null];
      switch (x[0]) {
        case "N": return modal ? N(a) : NOT(a);
        case "A": return modal ? AND(a, b) : A(a, b);
        case "O": return modal ? OR(a, b) : O(a, b);
        case "L": return L(a);
        default: return C(a, b);
      }
    };
    return go(t);
  }

  /* Parse infix (p -> q, ~p, p & q, p | q, ⊥, []p, <>p, <->, with Unicode alternatives) or
   * Łukasiewicz Polish notation (C, N, K, A, E, L, M). Returns a canonical formula. */
  function parse(src) {
    const s = src.trim();
    if (!s) throw new Error("empty formula");
    if (/^[CNKAELM]+[p-w][CNKAELMp-w]*$/.test(s)) return canon(parsePolish(s));
    const toks = [];
    const re = /\s*(<->|↔|->|→|=>|<>|◇|\[\]|□|¬|~|!|∧|&|\/\\|∨|\||\\\/|⊥|_\|_|\(|\)|[a-z][a-z0-9']*)/y;
    let pos = 0;
    while (pos < s.length) {
      re.lastIndex = pos;
      const m = re.exec(s);
      if (!m) throw new Error(`can't read "${s.slice(pos, pos + 8)}"`);
      toks.push(m[1]);
      pos = re.lastIndex;
      while (pos < s.length && s[pos] === " ") pos++;
    }
    const names = new Map();
    let i = 0;
    const peek = () => toks[i], next = () => toks[i++];
    const BIN = { "<->": 0, "↔": 0, "->": 1, "→": 1, "=>": 1, "∨": 2, "|": 2, "\\/": 2, "∧": 3, "&": 3, "/\\": 3 };
    function unary() {
      const t = next();
      if (t === undefined) throw new Error("formula ends too early");
      if (["¬", "~", "!"].includes(t)) return N(unary());
      if (["□", "[]"].includes(t)) return L(unary());
      if (["◇", "<>"].includes(t)) return N(L(N(unary())));
      if (["⊥", "_|_", "bot", "false"].includes(t)) return F;
      if (t === "(") { const e = expr(0); if (next() !== ")") throw new Error("missing )"); return e; }
      if (/^[a-z]/.test(t)) { if (!names.has(t)) names.set(t, names.size); return names.get(t); }
      throw new Error(`unexpected "${t}"`);
    }
    function expr(minPrec) {
      let left = unary();
      while (peek() in BIN && BIN[peek()] >= minPrec) {
        const op = next(), p = BIN[op];
        const right = expr(p === 1 ? p : p + 1);          // -> is right-associative
        left = p === 0 ? A(C(left, right), C(right, left)) : p === 1 ? C(left, right) : p === 2 ? O(left, right) : A(left, right);
      }
      return left;
    }
    const e = expr(0);
    if (i !== toks.length) throw new Error(`unexpected "${toks[i]}"`);
    return canon(normalize(e));
  }
  function parsePolish(s) {
    let i = 0;
    function r() {
      const ch = s[i++];
      if (ch === undefined) throw new Error("formula ends too early");
      if (ch === "C") { const a = r(); return C(a, r()); }
      if (ch === "K") { const a = r(); return A(a, r()); }
      if (ch === "A") { const a = r(); return O(a, r()); }
      if (ch === "E") { const a = r(), b = r(); return A(C(a, b), C(b, a)); }
      if (ch === "N") return N(r());
      if (ch === "L") return L(r());
      if (ch === "M") return N(L(N(r())));
      const v = LETTERS.indexOf(ch);
      if (v < 0) throw new Error(`unexpected "${ch}"`);
      return v;
    }
    const t = r();
    if (i !== s.length) throw new Error("trailing text");
    return normalize(t);
  }

  // ------------------------------------------------------------ propositional deciders
  // Formulas interned as ints: atoms are negative (⊥ is -1, variable v is -(v + 2)).
  function interner() {
    const ids = new Map(), OP = [], LF = [], RT = [];
    const mk = (o, a, b) => { const k = o + a + "," + b; let id = ids.get(k); if (id === undefined) { id = OP.length; ids.set(k, id); OP.push(o); LF.push(a); RT.push(b); } return id; };
    const tr = t => typeof t === "number" ? -(t + 2) : t[0] === "F" ? -1 : t[0] === "N" ? mk("C", tr(t[1]), -1) : mk(t[0], tr(t[1]), tr(t[2]));
    return { mk, tr, OP, LF, RT };
  }
  function tautology(t) {
    const k = nvars(t);
    const ev = (x, a) => {
      if (typeof x === "number") return (a >> x & 1) === 1;
      switch (x[0]) {
        case "F": return false;
        case "N": return !ev(x[1], a);
        case "A": return ev(x[1], a) && ev(x[2], a);
        case "O": return ev(x[1], a) || ev(x[2], a);
        default: return !ev(x[1], a) || ev(x[2], a);
      }
    };
    for (let a = 0; a < 1 << k; a++) if (!ev(t, a)) return false;
    return true;
  }
  /* G4ip (Dyckhoff 1992) for →, ∧, ∨, ⊥. Minimal logic is the same calculus with ⊥ read as an
   * ordinary atom (no explosion). Every rule shrinks the sequent, so search terminates. */
  function makeG4ip(explosion) {
    const { mk, tr, OP, LF, RT } = interner(), BOT = -1;
    const memo = new Map();
    function prove(gamma, goal) {
      const g = [...new Set(gamma)].sort((a, b) => a - b), k = g.join(",") + "|" + goal;
      if (memo.has(k)) return memo.get(k);
      memo.set(k, false);
      const r = step(new Set(g), goal);
      memo.set(k, r);
      return r;
    }
    function step(g, goal) {
      if (goal >= 0 && OP[goal] === "C") { g.add(LF[goal]); return prove([...g], RT[goal]); }
      if (goal >= 0 && OP[goal] === "A") return prove([...g], LF[goal]) && prove([...g], RT[goal]);
      for (let changed = true; changed;) {                 // invertible left rules
        changed = false;
        if ((explosion && g.has(BOT)) || g.has(goal)) return true;
        for (const f of g) {
          if (f < 0) continue;
          const o = OP[f], a = LF[f], b = RT[f];
          if (o === "A") { g.delete(f); g.add(a); g.add(b); changed = true; break; }
          if (o === "O") { g.delete(f); return prove([...g, a], goal) && prove([...g, b], goal); }
          if (a < 0) {
            if (explosion && a === BOT) { g.delete(f); changed = true; break; }
            if (g.has(a)) { g.delete(f); g.add(b); changed = true; break; }
          } else if (OP[a] === "A") { g.delete(f); g.add(mk("C", LF[a], mk("C", RT[a], b))); changed = true; break; }
          else if (OP[a] === "O") { g.delete(f); g.add(mk("C", LF[a], b)); g.add(mk("C", RT[a], b)); changed = true; break; }
        }
      }
      if (goal >= 0 && OP[goal] === "O" && (prove([...g], LF[goal]) || prove([...g], RT[goal]))) return true;
      const arr = [...g];
      for (const f of arr) {
        if (f < 0 || OP[f] !== "C" || LF[f] < 0 || OP[LF[f]] !== "C") continue;
        const c = LF[LF[f]], d = RT[LF[f]], b = RT[f], rest = arr.filter(x => x !== f);
        if (prove([...rest, mk("C", d, b), c], d) && prove([...rest, b], goal)) return true;
      }
      return false;
    }
    return t => prove([], tr(t));
  }
  /* Sequent search for the substructural floors. Contexts are multisets (exchange is always
   * allowed); ∧ and ∨ are the additive connectives; ⊥ is an atom with no rules.
   *   weak        weakening is allowed (absorbed into the axiom: Γ, A ⊢ A)
   *   dupBudget   how many times one branch may contract (copy) a hypothesis
   *   copyBudget  how many times one branch may take a copy of an unrestricted hypothesis
   * Unrestricted hypotheses (theta) are theorems of the base: like linear logic's !A they can
   * be used any number of times, or not at all. Without contraction every rule shrinks the
   * sequent, so search for plain theorems is exact for linear and affine logic. Contraction
   * and theta copies are bounded, which keeps search sound but makes it incomplete. */
  function makeSequent(weak, dupBudget, copyBudget = 3, stepLimit = Infinity) {
    const { tr, OP, LF, RT } = interner();
    const memo = new Map();
    let TH = [], steps = 0;
    const sorted = a => a.sort((x, y) => x - y);
    function prove(ctx, goal, d, c) {
      const k = ctx.join(",") + "|" + goal + "|" + d + "|" + c;
      if (memo.has(k)) return memo.get(k);
      if (++steps > stepLimit) throw STEP_OUT;
      memo.set(k, false);
      const r = step(ctx, goal, d, c);
      memo.set(k, r);
      return r;
    }
    function step(ctx, goal, d, c) {
      if (goal >= 0 && OP[goal] === "C") return prove(sorted([...ctx, LF[goal]]), RT[goal], d, c);
      if (goal >= 0 && OP[goal] === "A") return prove(ctx, LF[goal], d, c) && prove(ctx, RT[goal], d, c);
      for (let i = 0; i < ctx.length; i++) {               // ∨ on the left is invertible
        const f = ctx[i];
        if (f >= 0 && OP[f] === "O") {
          const rest = ctx.filter((_, j) => j !== i);
          return prove(sorted([...rest, LF[f]]), goal, d, c) && prove(sorted([...rest, RT[f]]), goal, d, c);
        }
      }
      if (weak ? ctx.includes(goal) : ctx.length === 1 && ctx[0] === goal) return true;
      if (goal >= 0 && OP[goal] === "O" && (prove(ctx, LF[goal], d, c) || prove(ctx, RT[goal], d, c))) return true;
      for (let i = 0; i < ctx.length; i++) {
        const f = ctx[i];
        if (f < 0 || (i > 0 && ctx[i - 1] === f)) continue;
        const rest = ctx.filter((_, j) => j !== i);
        for (const keep of d > 0 ? [false, true] : [false]) {    // keep = contract f first
          const base = keep ? ctx : rest, dd = keep ? d - 1 : d;
          if (OP[f] === "A") {
            if (prove(sorted([...base, LF[f]]), goal, dd, c) || prove(sorted([...base, RT[f]]), goal, dd, c)) return true;
          } else if (OP[f] === "C" && split(base, LF[f], RT[f], goal, dd, c)) return true;
        }
      }
      if (c > 0) for (const th of TH) if (prove(sorted([...ctx, th]), goal, d, c - 1)) return true;
      return false;
    }
    // →L: share the other hypotheses between  Γ1 ⊢ a  and  Γ2, b ⊢ goal.
    function split(base, a, b, goal, d, c) {
      const items = [];
      for (const x of base) { const last = items[items.length - 1]; if (last && last[0] === x) last[1]++; else items.push([x, 1]); }
      const left = [], right = [];
      const rec = (i, dd) => {
        if (i === items.length) return prove(sorted(left.slice()), a, dd, c) && prove(sorted([...right, b]), goal, dd, c);
        const [x, n] = items[i];
        for (let jl = 0; jl <= n; jl++) {
          for (const extra of dd > 0 && jl > 0 ? [0, 1] : [0]) {   // extra: one copy goes to both sides
            const jr = n - jl + extra;
            for (let q = 0; q < jl; q++) left.push(x);
            for (let q = 0; q < jr; q++) right.push(x);
            const ok = rec(i + 1, dd - extra);
            left.length -= jl; right.length -= jr;
            if (ok) return true;
          }
        }
        return false;
      };
      return rec(0, d);
    }
    return (t, theta = []) => { TH = theta.map(tr); return prove([], tr(t), dupBudget, TH.length ? copyBudget : 0); };
  }
  const SUBSTRUCTURAL = { linear: [false, 0], affine: [true, 0], relevant: [false, 2] };
  const STEP_OUT = new Error("step limit");
  // Instance search may meet sequents whose proof search blows up. A search that runs past
  // this many steps counts as "no proof found" (sound: it only loses proofs). Infinity = exact.
  let DERIVE_STEP_LIMIT = Infinity;
  /** Does the target follow from theorems `theta` of a base whose decidable part is `logic`? */
  function derivable(theta, target, logic) {
    if (!(logic in SUBSTRUCTURAL)) return isTheorem(theta.reduceRight((acc, x) => C(x, acc), target), logic);
    const k = logic + "|" + theta.map(key).join(";") + "|" + key(target);
    if (DECIDE_CACHE.has(k)) return DECIDE_CACHE.get(k);
    let r;
    try { r = makeSequent(...SUBSTRUCTURAL[logic], 3, DERIVE_STEP_LIMIT)(target, theta); }
    catch (e) { if (e === STEP_OUT) return false; throw e; }
    DECIDE_CACHE.set(k, r);
    return r;
  }
  const DECIDE_CACHE = new Map();
  function isTheorem(t, logic) {
    const k = logic + ":" + key(t);
    if (DECIDE_CACHE.has(k)) return DECIDE_CACHE.get(k);
    let r;
    if (logic === "classical") r = tautology(t);
    else if (logic === "minimal" || logic === "intuitionistic") r = makeG4ip(logic === "intuitionistic")(t);
    else if (logic === "LC") r = holdsIn(t, goedelChain(nvars(t) + 2));
    else if (logic in SUBSTRUCTURAL) r = makeSequent(...SUBSTRUCTURAL[logic])(t);
    else if (logic === "K" || logic === "S4") r = modalValid(t, logic);
    else if (logic === "S5") r = (nvars(t) <= 4 && s5Valid(t)) || modalValid(t, "S4");
    else throw new Error(logic);
    DECIDE_CACHE.set(k, r);
    return r;
  }

  // ------------------------------------------------------------ modal tableaux (K, S4)
  function makeNNF() {
    const ids = new Map(), node = [];
    const mk = (tag, a, b = -1) => { const k = tag + a + "," + b; let id = ids.get(k); if (id === undefined) { id = node.length; ids.set(k, id); node.push([tag, a, b]); } return id; };
    function nnf(t, pos) {
      if (typeof t === "number") return mk(pos ? "v" : "n", t);
      if (t[0] === "F") return mk(pos ? "0" : "1", 0);
      if (t[0] === "N") return nnf(t[1], !pos);
      if (t[0] === "C") return pos ? mk("|", nnf(t[1], false), nnf(t[2], true)) : mk("&", nnf(t[1], true), nnf(t[2], false));
      return pos ? mk("B", nnf(t[1], true)) : mk("D", nnf(t[1], false));
    }
    return { nnf, node, mk };
  }
  function* saturate(S, node, reflexive, mk) {
    const stack = [{ f: new Set(S), done: new Set() }];
    while (stack.length) {
      const { f, done } = stack.pop();
      let clash = false;
      for (const x of f) { const [t, a] = node[x]; if (t === "0" || (t === "v" && f.has(mk("n", a)))) { clash = true; break; } }
      if (clash) continue;
      let todo = -1;
      for (const x of f) { const t = node[x][0]; if (!done.has(x) && (t === "&" || (reflexive && t === "B"))) { todo = x; break; } }
      if (todo < 0) for (const x of f) if (!done.has(x) && node[x][0] === "|") { todo = x; break; }
      if (todo < 0) { yield f; continue; }
      const [t, a, b] = node[todo];
      const d2 = new Set(done); d2.add(todo);
      if (t === "&") { const f2 = new Set(f); f2.add(a); f2.add(b); stack.push({ f: f2, done: d2 }); }
      else if (t === "|") {
        if (f.has(a) || f.has(b)) stack.push({ f, done: d2 });
        else { const f2 = new Set(f); f2.add(b); stack.push({ f: f2, done: d2 }); const f1 = new Set(f); f1.add(a); stack.push({ f: f1, done: d2 }); }
      } else { const f2 = new Set(f); f2.add(a); stack.push({ f: f2, done: d2 }); }
    }
  }
  function modalValid(t, logic) {
    const { nnf, node, mk } = makeNNF();
    const start = [nnf(t, false)];
    const skey = S => [...S].sort((x, y) => x - y).join(",");
    if (logic === "K") {
      const memo = new Map();
      const sat = S => {
        const k = skey(S);
        if (memo.has(k)) return memo.get(k);
        let r = false;
        for (const w of saturate(S, node, false, mk)) {
          const boxes = [...w].filter(x => node[x][0] === "B").map(x => node[x][1]);
          if ([...w].filter(x => node[x][0] === "D").every(x => sat([node[x][1], ...boxes]))) { r = true; break; }
        }
        memo.set(k, r);
        return r;
      };
      return !sat(start);
    }
    // S4: ancestor-subset blocking; cache results that did not use blocking.
    const cache = new Map();
    const sat = (S, anc) => {
      const k = skey(S);
      if (cache.has(k)) return [cache.get(k), false];
      let used = false;
      for (const w of saturate(S, node, true, mk)) {
        const boxes = [...w].filter(x => node[x][0] === "B");
        let ok = true;
        for (const x of w) {
          if (node[x][0] !== "D" || w.has(node[x][1])) continue;
          const core = new Set([...boxes, node[x][1]]);
          if ([...anc, w].some(a => [...core].every(y => a.has(y)))) { used = true; continue; }
          const [r, b] = sat(core, [...anc, w]);
          used = used || b;
          if (!r) { ok = false; break; }
        }
        if (ok) { if (!used) cache.set(k, true); return [true, used]; }
      }
      if (!used) cache.set(k, false);
      return [false, used];
    };
    return !sat(start, [])[0];
  }
  function s5Valid(t) {
    const k = nvars(t), W = 1 << k, FULL = (1 << W) - 1;
    for (let present = 1; present <= FULL; present++) {
      const ev = x => {
        if (typeof x === "number") { let m = 0; for (let w = 0; w < W; w++) if (w >> x & 1) m |= 1 << w; return m; }
        if (x[0] === "F") return 0;
        if (x[0] === "N") return ~ev(x[1]) & FULL;
        if (x[0] === "C") return (~ev(x[1]) | ev(x[2])) & FULL;
        return (ev(x[1]) & present) === present ? FULL : 0;
      };
      if ((ev(t) & present) !== present) return false;
    }
    return true;
  }
  function godel(t) {
    if (typeof t === "number") return L(t);
    if (t[0] === "F") return t;
    if (t[0] === "N") return L(N(godel(t[1])));
    return L(C(godel(t[1]), godel(t[2])));
  }

  // ------------------------------------------------------------ propositional models (algebras)
  /* A model is a finite algebra: values 0..n-1 with tables for →, ∧, ∨, a value for ⊥, and a
   * set of designated ("true") values. It is a model of the core when every core axiom is
   * always designated and the rules (modus ponens, adjunction) keep designated values
   * designated; then nothing it falsifies can be proved. */
  function compile(x) {
    if (typeof x === "number") return (m, a) => a[x];
    if (x[0] === "F") return m => m.bot;
    const p = compile(x[1]), q = x.length > 2 ? compile(x[2]) : null;
    switch (x[0]) {
      case "A": return (m, a) => m.meet[p(m, a) * m.n + q(m, a)];
      case "O": return (m, a) => m.join[p(m, a) * m.n + q(m, a)];
      case "N": return (m, a) => m.imp[p(m, a) * m.n + m.bot];
      default: return (m, a) => m.imp[p(m, a) * m.n + q(m, a)];
    }
  }
  function firstFailure(t, m, ev = compile(t)) {
    const k = nvars(t), n = m.n, a = new Array(k).fill(0);
    while (true) {
      if (!(m.des >> ev(m, a) & 1)) return a;
      let j = 0;
      while (j < k && a[j] === n - 1) a[j++] = 0;
      if (j === k) return null;
      a[j]++;
    }
  }
  function holdsIn(t, m, ev) { return firstFailure(t, m, ev) === null; }
  function failingAssignment(t, m) {
    const a = firstFailure(t, m);
    if (!a) return null;
    const o = {};
    a.forEach((v, j) => { o[LETTERS[j]] = m.labels[v]; });
    return o;
  }
  function latticeOps(le) {
    const n = le.length, meet = new Int8Array(n * n), join = new Int8Array(n * n);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const lo = [...Array(n).keys()].filter(k => le[k][i] && le[k][j]), hi = [...Array(n).keys()].filter(k => le[i][k] && le[j][k]);
      meet[i * n + j] = lo.find(k => lo.every(l => le[l][k]));
      join[i * n + j] = hi.find(k => hi.every(l => le[k][l]));
    }
    return { meet, join };
  }
  const chainLe = n => [...Array(n)].map((_, i) => [...Array(n)].map((_, j) => i <= j));
  function fromCovers(n, covers) {
    const le = [...Array(n)].map((_, i) => [...Array(n)].map((_, j) => i === j));
    for (const [a, b] of covers) le[a][b] = true;
    for (let k = 0; k < n; k++) for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (le[i][k] && le[k][j]) le[i][j] = true;
    return le;
  }
  function goedelChain(n) {
    const { meet, join } = latticeOps(chainLe(n)), imp = new Int8Array(n * n);
    for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) imp[a * n + b] = a <= b ? n - 1 : b;
    return { n, imp, meet, join, bot: 0, des: 1 << (n - 1) };
  }
  function permutations(n) {
    if (n === 0) return [[]];
    const out = [];
    for (const p of permutations(n - 1)) for (let i = 0; i <= p.length; i++) out.push([...p.slice(0, i), n - 1, ...p.slice(i)]);
    return out;
  }
  // Every partial order on `size` points, one per isomorphism class.
  function posets(size) {
    const pairs = [];
    for (let i = 0; i < size; i++) for (let j = 0; j < size; j++) if (i !== j) pairs.push([i, j]);
    const perms = permutations(size), out = [], seen = new Set();
    for (let bits = 0; bits < 1 << pairs.length; bits++) {
      const le = [...Array(size)].map((_, i) => [...Array(size)].map((_, j) => i === j));
      pairs.forEach(([i, j], k) => { if (bits >> k & 1) le[i][j] = true; });
      if (pairs.some(([i, j]) => le[i][j] && le[j][i])) continue;
      let trans = true;
      for (let i = 0; i < size && trans; i++) for (let j = 0; j < size && trans; j++) for (let k = 0; k < size && trans; k++)
        if (le[i][j] && le[j][k] && !le[i][k]) trans = false;
      if (!trans) continue;
      const kk = perms.map(p => p.map(i => p.map(j => le[i][j] ? 1 : 0).join("")).join("/")).sort()[0];
      if (!seen.has(kk)) { seen.add(kk); out.push(le); }
    }
    return out;
  }
  // Heyting algebras of down-sets of small posets (Kripke models), with every choice of ⊥:
  // ⊥ = 0 gives models of intuitionistic logic, other choices models of minimal logic.
  function heytingModels(maxPoints) {
    const out = [];
    for (let size = 1; size <= maxPoints; size++) for (const le of posets(size)) {
      const below = [...Array(size)].map((_, i) => { let m = 0; for (let j = 0; j < size; j++) if (le[j][i]) m |= 1 << j; return m; });
      const elems = [];
      for (let m = 0; m < 1 << size; m++) { let ok = true; for (let i = 0; i < size; i++) if ((m >> i & 1) && (below[i] & ~m)) ok = false; if (ok) elems.push(m); }
      const pop = x => x.toString(2).split("1").length - 1;
      elems.sort((a, b) => pop(a) - pop(b) || a - b);
      const index = new Map(elems.map((m, k) => [m, k]));
      const n = elems.length, imp = new Int8Array(n * n), meet = new Int8Array(n * n), join = new Int8Array(n * n);
      elems.forEach((ma, a) => elems.forEach((mb, b) => {
        let mc = 0;
        for (let x = 0; x < size; x++) if ((below[x] & ma & ~mb) === 0) mc |= 1 << x;
        imp[a * n + b] = index.get(mc);
        meet[a * n + b] = index.get(ma & mb);
        join[a * n + b] = index.get(ma | mb);
      }));
      const labels = n > 2 ? ["0", ...[...Array(n - 2)].map((_, k) => "a" + (k + 1)), "1"] : ["0", "1"];
      const isChain = elems.every((m, k) => k === 0 || (m & elems[k - 1]) === elems[k - 1]);
      for (let bot = 0; bot < n; bot++)
        out.push({ n, imp, meet, join, bot, des: 1 << (n - 1), labels, chain: isChain, name: n === 2 ? "Boolean" : `Heyting(${n})` });
    }
    return out;
  }
  // Every implication table on a 2- or 3-element chain (∧ = min, ∨ = max), with every
  // designated up-set and every ⊥. Most are weird; only those that model the core are kept.
  function chainModels(n) {
    const out = [], { meet, join } = latticeOps(chainLe(n)), labels = [...Array(n)].map((_, i) => String(i));
    for (let lo = 1; lo < n; lo++) {
      const des = ((1 << n) - 1) & ~((1 << lo) - 1);
      for (let t = 0; t < n ** (n * n); t++) {
        const imp = new Int8Array(n * n);
        let r = t;
        for (let c = 0; c < n * n; c++) { imp[c] = r % n; r = Math.floor(r / n); }
        const probe = { n, imp, meet, join, bot: 0, des, labels, chain: true, name: `${n}-valued` };
        if (!coreModel(probe)) continue;
        for (let bot = 0; bot < n; bot++) out.push({ ...probe, bot });
      }
    }
    return out;
  }
  /* Commutative residuated lattices on a small lattice: a commutative, associative "fusion"
   * x·y with unit e that preserves joins; a → b is the largest z with z·a ≤ b, and the
   * designated values are those ≥ e. This is the standard algebraic semantics of the core:
   * x·y ≤ x (e is the top) validates weakening, x ≤ x·x validates contraction. */
  function residuatedModels(le, labels, name) {
    const n = le.length, { meet, join } = latticeOps(le), out = [];
    const bot0 = [...Array(n).keys()].find(i => le[i].every(x => x)), isChain = le.every((r, i) => r.every((x, j) => x || le[j][i]));
    for (let e = 0; e < n; e++) {
      if (e === bot0) continue;
      const others = [...Array(n).keys()].filter(i => i !== e && i !== bot0), free = [];
      for (let i = 0; i < others.length; i++) for (let j = i; j < others.length; j++) free.push([others[i], others[j]]);
      for (let t = 0; t < n ** free.length; t++) {
        const mul = new Int8Array(n * n);
        for (let x = 0; x < n; x++) { mul[e * n + x] = mul[x * n + e] = x; }
        for (let x = 0; x < n; x++) { mul[bot0 * n + x] = mul[x * n + bot0] = bot0; }
        let r = t;
        for (const [i, j] of free) { const v = r % n; r = (r - v) / n; mul[i * n + j] = mul[j * n + i] = v; }
        let ok = true;
        for (let x = 0; x < n && ok; x++) for (let y = 0; y < n && ok; y++) for (let z = y + 1; z < n && ok; z++)
          if (mul[x * n + join[y * n + z]] !== join[mul[x * n + y] * n + mul[x * n + z]]) ok = false;
        for (let x = 0; x < n && ok; x++) for (let y = 0; y < n && ok; y++) for (let z = 0; z < n && ok; z++)
          if (mul[mul[x * n + y] * n + z] !== mul[x * n + mul[y * n + z]]) ok = false;
        if (!ok) continue;
        const imp = new Int8Array(n * n);
        for (let x = 0; x < n && ok; x++) for (let y = 0; y < n; y++) {
          let best = bot0;
          for (let z = 0; z < n; z++) if (le[mul[z * n + x]][y]) best = join[best * n + z];
          if (!le[mul[best * n + x]][y]) { ok = false; break; }
          imp[x * n + y] = best;
        }
        if (!ok) continue;
        let des = 0;
        for (let x = 0; x < n; x++) if (le[e][x]) des |= 1 << x;
        for (let bot = 0; bot < n; bot++) out.push({ n, imp, meet, join, bot, des, labels, chain: isChain, name });
      }
    }
    return out;
  }
  const PROP_CORE = [
    C(0, 0),                                             // identity
    C(C(1, 2), C(C(0, 1), C(0, 2))),                     // composition
    C(C(0, C(1, 2)), C(1, C(0, 2))),                     // exchange
    C(A(0, 1), 0), C(A(0, 1), 1),                        // ∧ elimination
    C(A(C(0, 1), C(0, 2)), C(0, A(1, 2))),               // ∧ introduction (with the adjunction rule)
    C(0, O(0, 1)), C(1, O(0, 1)),                        // ∨ introduction
    C(A(C(0, 2), C(1, 2)), C(O(0, 1), 2)),               // ∨ elimination
  ];
  const CORE_EVAL = PROP_CORE.map(compile);
  function coreModel(m) {
    const n = m.n;
    for (let a = 0; a < n; a++) {
      if (!(m.des >> a & 1)) continue;
      for (let b = 0; b < n; b++) {
        if ((m.des >> m.imp[a * n + b] & 1) && !(m.des >> b & 1)) return false;            // modus ponens
        if ((m.des >> b & 1) && !(m.des >> m.meet[a * n + b] & 1)) return false;           // adjunction
      }
    }
    return PROP_CORE.every((t, i) => holdsIn(t, m, CORE_EVAL[i]));
  }
  /* A few larger algebras with weakening (x·y ≤ x), found by searching every residuated
   * structure on the 6- and 7-element lattices. No smaller algebra with weakening breaks
   * distribution, or has double negation without linearity, so the built-in families
   * can't separate those. [lattice covers, ⊥, → table (row-major)] */
  const SEARCHED = [
    ["01 12 13 14 25 35 45 56", 0, "6666666566666625655663556566455566615555660123456"],   // no distribution; explosion, double negation
    ["01 02 03 14 24 34 45", 4, "555555454455445455444555444455012345"],                  // no distribution; excluded middle
    ["01 12 13 14 25 35 45 56", 0, "6666666066666605655660556566055566605555660123456"],   // no distribution; explosion, weak excluded middle
    ["01 12 13 24 34 45", 0, "555555455555245455344555144455012345"],                     // double negation without linearity
  ];
  function searchedModel([covers, bot, imp]) {
    const pairs = covers.split(" ").map(s => [+s[0], +s[1]]), n = Math.max(...pairs.flat()) + 1, le = fromCovers(n, pairs);
    const { meet, join } = latticeOps(le);
    const labels = n === 6 ? ["0", "a", "b", "c", "d", "1"] : ["0", "a", "b", "c", "d", "e", "1"];
    return { n, imp: Int8Array.from(imp, Number), meet, join, bot, des: 1 << (n - 1), labels, chain: false, name: `${n}-element algebra (found by search)` };
  }
  function propModels() {
    const lattices = [
      ...[2, 3, 4, 5].map(n => [chainLe(n), [...Array(n)].map((_, i) => String(i)), `${n}-element chain`]),
      [fromCovers(4, [[0, 1], [0, 2], [1, 3], [2, 3]]), ["0", "a", "b", "1"], "four-element square"],
      [fromCovers(5, [[0, 1], [1, 2], [1, 3], [2, 4], [3, 4]]), ["0", "a", "b", "c", "1"], "five-element lattice"],
      [fromCovers(5, [[0, 1], [0, 2], [1, 3], [2, 3], [3, 4]]), ["0", "a", "b", "c", "1"], "five-element lattice"],
      [fromCovers(5, [[0, 1], [1, 2], [2, 4], [0, 3], [3, 4]]), ["0", "a", "b", "c", "1"], "pentagon N5 (not distributive)"],
      [fromCovers(5, [[0, 1], [0, 2], [0, 3], [1, 4], [2, 4], [3, 4]]), ["0", "a", "b", "c", "1"], "diamond M3 (not distributive)"],
    ];
    const all = [...heytingModels(4), ...chainModels(2), ...chainModels(3), ...lattices.flatMap(([le, lab, nm]) => residuatedModels(le, lab, nm)),
                 ...SEARCHED.map(searchedModel)];
    const out = [], seen = new Set();
    for (const m of all) {
      const k = [m.n, m.bot, m.des, m.imp.join(""), m.meet.join(""), m.join.join("")].join("|");
      if (seen.has(k) || !coreModel(m)) continue;
      seen.add(k);
      out.push(m);
    }
    // Small models first, so the certificate shown for a refutation is the simplest one.
    return out.sort((a, b) => a.n - b.n);
  }
  function modelDict(m) {
    const rows = t => [...Array(m.n).keys()].map(a => [...t.slice(a * m.n, a * m.n + m.n)]);
    const des = [];
    for (let v = 0; v < m.n; v++) if (m.des >> v & 1) des.push(v);
    return { name: m.name, values: m.labels, designated: des, imp: rows(m.imp), bot: m.bot, chain: !!m.chain,
             meet: m.chain ? null : rows(m.meet), join: m.chain ? null : rows(m.join) };
  }

  // ------------------------------------------------------------ Kripke frames
  function allFrames(maxWorlds) {
    const out = [];
    for (let n = 1; n <= maxWorlds; n++) for (let bits = 0; bits < 1 << (n * n); bits++) {
      const succ = new Uint8Array(n);
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (bits >> (i * n + j) & 1) succ[i] |= 1 << j;
      out.push({ n, succ });
    }
    return out;
  }
  function frameEval(f, val, full) {
    const n = f.n;
    const ev = x => {
      if (typeof x === "number") return val[x];
      if (x[0] === "F") return 0;
      if (x[0] === "N") return ~ev(x[1]) & full;
      if (x[0] === "C") return (~ev(x[1]) | ev(x[2])) & full;
      const s = ev(x[1]);
      let r = 0;
      for (let w = 0; w < n; w++) if ((f.succ[w] & ~s & full) === 0) r |= 1 << w;
      return r;
    };
    return ev;
  }
  function frameValid(t, f) {
    const k = nvars(t), n = f.n, full = (1 << n) - 1, total = 1 << (n * k), val = new Array(k), ev = frameEval(f, val, full);
    for (let c = 0; c < total; c++) {
      for (let j = 0; j < k; j++) val[j] = (c >> (n * j)) & full;
      if (ev(t) !== full) return false;
    }
    return true;
  }
  function frameFailing(t, f) {
    const k = nvars(t), n = f.n, full = (1 << n) - 1, val = new Array(k), ev = frameEval(f, val, full);
    for (let c = 0; c < 1 << (n * k); c++) {
      for (let j = 0; j < k; j++) val[j] = (c >> (n * j)) & full;
      const v = ev(t);
      if (v !== full) {
        const world = [...Array(n).keys()].find(w => !(v >> w & 1));
        const valuation = {};
        for (let j = 0; j < k; j++) valuation[LETTERS[j]] = [...Array(n).keys()].filter(w => val[j] >> w & 1);
        return { world, valuation };
      }
    }
    return null;
  }
  function frameDict(f) {
    const arrows = [];
    for (let i = 0; i < f.n; i++) for (let j = 0; j < f.n; j++) if (f.succ[i] >> j & 1) arrows.push([i, j]);
    return { worlds: f.n, arrows };
  }

  // ------------------------------------------------------------ the two languages
  // [key, short name, formula, what it says, structural?]
  const PROP_PRINCIPLES = [
    ["K", "weakening", "p -> (q -> p)", "an unused assumption does no harm", true],
    ["W", "contraction", "(p -> (p -> q)) -> (p -> q)", "an assumption may be used twice", true],
    ["EFQ", "explosion", "⊥ -> p", "from a contradiction, anything follows"],
    ["DNE", "double negation", "~~p -> p", "not-not-p gives p"],
    ["LEM", "excluded middle", "p | ~p", "every statement is true or false"],
    ["WLEM", "weak excluded middle", "~p | ~~p", "every statement is refutable or irrefutable"],
    ["LIN", "linearity", "(p -> q) | (q -> p)", "of any two statements, one implies the other (Dummett)"],
    ["PEIRCE", "Peirce's law", "((p -> q) -> p) -> p", "classical, stated with implication only"],
    ["NC", "non-contradiction", "~(p & ~p)", "nothing is both true and false"],
    ["DIST", "distribution", "(p & (q | r)) -> ((p & q) | (p & r))", "'and' distributes over 'or'"],
  ];
  const PROP = {
    kind: "propositional", floorName: "linear", floorKeys: ["K", "W"],
    floor: PROP_CORE,
    // Hidden principles used to tell which decision procedure applies to a base.
    rungKeys: { K: "p -> (q -> p)", W: "(p -> (p -> q)) -> (p -> q)", EFQ: "⊥ -> p", DNE: "~~p -> p", LIN: "(p -> q) | (q -> p)", ALL: "p" },
    rung(proves) {
      const k = proves("K"), w = proves("W");
      if (!k || !w) return k ? "affine" : w ? "relevant" : "linear";
      if (proves("DNE")) return "classical";                  // minimal + DNE proves explosion
      if (proves("EFQ")) return proves("LIN") ? "LC" : "intuitionistic";
      return "minimal";
    },
    // Principles a decider already includes, so instance search needn't use them.
    absorbed(rung) {
      const out = ["K", "W"];
      if (["intuitionistic", "LC", "classical"].includes(rung)) out.push("EFQ");
      if (rung === "LC") out.push("LIN");
      return out;
    },
    floorTheorem: t => isTheorem(t, "linear"),
    special: { "minimal:EFQ": "intuitionistic", "minimal:DNE": "classical", "minimal:EFQ+LIN": "Gödel–Dummett", "minimal:EFQ+WLEM": "Jankov" },
    describe(base, label = k => k) {
      const has = k => base.includes(k);
      const floor = has("K") ? (has("W") ? "minimal" : "affine") : has("W") ? "relevant" : "linear";
      const rest = base.filter(k => k !== "K" && k !== "W");
      const sp = this.special[floor + ":" + rest.join("+")];
      if (sp) return sp;
      if (floor === "minimal" && rest[0] === "EFQ") return "intuitionistic + " + rest.slice(1).map(label).join(" + ");
      return rest.length ? floor + " + " + rest.map(label).join(" + ") : floor;
    },
    weakest(t) {
      if (isTheorem(t, "linear")) return "linear";
      const aff = isTheorem(t, "affine"), rel = isTheorem(t, "relevant");
      if (aff || rel) return aff && rel ? "affine and relevant" : aff ? "affine" : "relevant";
      return ["minimal", "intuitionistic", "classical"].find(l => isTheorem(t, l)) || "not classical";
    },
    pool(target) {
      const out = [], seen = new Set();
      const push = x => { const k = key(x); if (!seen.has(k)) { seen.add(k); out.push(x); } };
      const vs = [...vars(target)].sort((a, b) => a - b);
      vs.forEach(push);
      push(F);
      for (const v of vs) { push(NOT(v)); push(NOT(NOT(v))); }
      (function walk(x) { if (typeof x !== "number" && x[0] !== "F") { push(x); x.slice(1).forEach(walk); } })(target);
      // Leftover goals: for a target H1 → (H2 → … → G), each Hi → G (what's left to show once
      // the other hypotheses are used up, e.g. in one branch of a proof by cases).
      const hyps = [];
      let g = target;
      while (typeof g !== "number" && g[0] === "C" && !isBot(g[2])) { hyps.push(g[1]); g = g[2]; }
      if (hyps.length > 1) for (const h of hyps) push(C(h, g));
      for (const a of vs) for (const b of vs) if (a !== b) { push(C(a, b)); push(A(a, b)); push(O(a, b)); }
      return out;
    },
  };
  PROP.catalog = PROP_PRINCIPLES.map(([k, name, src, note, structural]) => ({ key: k, name, formula: parse(src), note, structural: !!structural }));
  const MODAL = {
    kind: "modal", floorName: "K", floorKeys: [],
    rungKeys: { T: "CLpp", "4": "CLpLLp", "5": "CMpLMp", ALL: "p", VER: "Lp" },
    rung(proves) { return proves("T") && proves("5") ? "S5" : proves("T") && proves("4") ? "S4" : "K"; },
    absorbed: () => [],
    floorTheorem: t => isTheorem(t, "K"),
    special: { "": "K", "T+4": "S4", "T+5": "S5", "T+B": "KTB", "T+4+G": "S4.2", L: "GL", G: "K.2", D: "KD", T: "KT" },
    describe(base, label = k => k) {
      const k = base.join("+");
      if (k in this.special) return this.special[k];
      return base.every(x => x.length === 1) ? "K" + base.join("") : "K + " + base.map(label).join(" + ");
    },
    weakest: t => isTheorem(t, "K") ? "K" : isTheorem(t, "S4") ? "S4" : "beyond S4",
    pool(target) {
      const out = [], seen = new Set();
      for (const v of [...vars(target)].sort((a, b) => a - b)) for (const a of [v, N(v)])
        for (const x of [a, L(a), M(a), L(L(a)), M(M(a)), L(M(a)), M(L(a)), AND(a, L(a)), C(L(a), a), C(a, L(a))]) {
          const k = key(x);
          if (!seen.has(k)) { seen.add(k); out.push(x); }
        }
      return out;
    },
  };

  function boxed(t, d) { let out = t, cur = t; for (let i = 0; i < d; i++) { cur = L(cur); out = AND(out, cur); } return out; }

  // ------------------------------------------------------------ the engine
  const MODEL_CACHE = {};
  function models(lang) {
    if (!MODEL_CACHE[lang.kind]) MODEL_CACHE[lang.kind] = lang.kind === "modal" ? allFrames(4) : propModels();
    return MODEL_CACHE[lang.kind];
  }
  const VALID_CACHE = new Map();
  /** Uint8Array over the language's models: does formula t hold (is it valid) there? */
  function validity(lang, t) {
    const k = lang.kind + ":" + key(t);
    if (VALID_CACHE.has(k)) return VALID_CACHE.get(k);
    const ms = models(lang), out = new Uint8Array(ms.length);
    const maxN = lang.kind === "modal" && nvars(t) >= 3 ? 3 : 99;        // keep 3-letter formulas fast
    const ev = lang.kind === "modal" ? null : compile(t);
    for (let i = 0; i < ms.length; i++) {
      if (ms[i].n > maxN) { out[i] = 2; continue; }                     // 2 = not evaluated
      out[i] = (lang.kind === "modal" ? frameValid(t, ms[i]) : holdsIn(t, ms[i], ev)) ? 1 : 0;
    }
    VALID_CACHE.set(k, out);
    return out;
  }

  /**
   * Compute a map. principles: [{key, name, formula (parsed), note}] (order kept).
   * opts.bases: explicit list of bases (arrays of keys); default: every set of the language's
   * structural principles (lang.floorKeys) combined with up to opts.maxCombo (3) of the other
   * principles that are not core theorems.
   * Returns { kind, principles, bases: [{axioms, name, cells}], nodes, edges, models, status }.
   */
  function computeMap(lang, principles, opts = {}) {
    const t0 = Date.now();
    const budget = opts.instanceBudgetMs ?? 400;
    const P = new Map(principles.map(p => [p.key, p]));
    const visible = principles.map(p => p.key);
    // Hidden rung witnesses, unless an identical visible principle exists.
    const rungAlias = {};
    for (const [rk, src] of Object.entries(lang.rungKeys)) {
      const f = parse(src), same = principles.find(p => key(p.formula) === key(f));
      if (same) rungAlias[rk] = same.key;
      else { const hk = "_" + rk; rungAlias[rk] = hk; P.set(hk, { key: hk, name: rk, formula: f, hidden: true }); }
    }
    const keys = [...P.keys()];
    const isCustom = k => !!(P.get(k) && P.get(k).custom);
    const describe = b => lang.describe(b, k => isCustom(k) ? P.get(k).name : k);
    const floorThm = {};
    for (const k of keys) floorThm[k] = lang.floorTheorem(P.get(k).formula);
    const extra = visible.filter(k => !floorThm[k]);
    const order = new Map(visible.map((k, i) => [k, i]));
    let bases = opts.bases;
    if (!bases) {
      const maxCombo = opts.maxCombo ?? 3;
      const fk = (lang.floorKeys || []).filter(k => extra.includes(k)), others = extra.filter(k => !fk.includes(k));
      const combos = [[]];
      const rec = (start, acc) => { for (let i = start; i < others.length; i++) { const nb = [...acc, others[i]]; combos.push(nb); if (nb.length < maxCombo) rec(i + 1, nb); } };
      rec(0, []);
      // Below the full floor, only opts.floorCombo principles at a time (keeps the map readable).
      const below = opts.floorCombo ?? maxCombo;
      bases = [];
      for (let mask = 0; mask < 1 << fk.length; mask++) {
        const fl = fk.filter((_, i) => mask >> i & 1);
        for (const cmb of combos) if (fl.length === fk.length || cmb.length <= below) bases.push([...fl, ...cmb].sort((x, y) => order.get(x) - order.get(y)));
      }
    }
    // Extra bases (e.g. the user's current set of assumptions, which may be larger than
    // maxCombo), kept in catalog order and without duplicates.
    if (opts.extraBases) {
      const seen = new Set(bases.map(b => b.join("+")));
      for (const b of opts.extraBases) {
        const nb = [...new Set(b)].filter(k => order.has(k) && !floorThm[k]).sort((x, y) => order.get(x) - order.get(y));
        if (!seen.has(nb.join("+"))) { seen.add(nb.join("+")); bases.push(nb); }
      }
    }
    const ms = models(lang);
    const ok0 = new Uint8Array(ms.length).fill(1);
    const valid = {};
    for (const k of keys) valid[k] = validity(lang, P.get(k).formula);
    const cells = new Map();
    const bkey = b => b.join("+");
    // 1. countermodels
    for (const b of bases) {
      const c = {};
      const ok = ok0.slice();
      for (const k of b) { const v = valid[k]; for (let i = 0; i < ms.length; i++) ok[i] &= v[i] === 1 ? 1 : 0; }
      for (const k of keys) {
        if (b.includes(k)) { c[k] = { status: "given" }; continue; }
        if (floorThm[k]) { c[k] = { status: "decided", by: lang.floorName }; continue; }
        const v = valid[k];
        let best = -1;
        for (let i = 0; i < ms.length; i++) if (ok[i] && v[i] === 0 && (best < 0 || ms[i].n < ms[best].n)) best = i;
        if (best >= 0) {
          const f = P.get(k).formula;
          c[k] = { status: "refuted", model: best, falsified_by: lang.kind === "modal" ? frameFailing(f, ms[best]) : failingAssignment(f, ms[best]) };
        } else c[k] = { status: "unknown" };
      }
      cells.set(bkey(b), c);
    }
    const proves = (c, k) => ["given", "proved", "chained", "instance", "decided"].includes(c[k] && c[k].status);
    const rungOf = c => lang.rung(rk => proves(c, rungAlias[rk]));
    // 2. closure: decide, chain, instances
    function decide() {
      let n = 0;
      for (const b of bases) {
        const c = cells.get(bkey(b)), rung = rungOf(c);
        if (rung === lang.floorName) continue;
        for (const k of keys) if (c[k].status === "unknown" && isTheorem(P.get(k).formula, rung)) { c[k] = { status: "decided", by: rung }; n++; }
      }
      return n;
    }
    function chain() {
      let n = 0, changed = true;
      while (changed) {
        changed = false;
        for (const b of bases) {
          const cb = cells.get(bkey(b));
          for (const b2 of bases) {
            if (b2 === b || !b2.every(k => proves(cb, k))) continue;
            const c2 = cells.get(bkey(b2));
            for (const k of keys) if (proves(c2, k) && !proves(cb, k)) {
              if (cb[k].status === "refuted") throw new Error(`inconsistent: ${bkey(b)} proves ${bkey(b2)} which proves ${k}, but ${k} is refuted`);
              cb[k] = { status: "chained", via: b2.slice() };
              n++; changed = true;
            }
          }
        }
      }
      return n;
    }
    /* Look for one or two substitution instances of the base's principles from which the
     * target follows in the base's decidable part, each instance usable any number of times
     * (it is a theorem). Every step of such a derivation is modus ponens or adjunction, so it
     * is a proof in the base. (Modal: a conjunction of boxed instances, checked in K.) */
    function instance(b, k) {
      const c = cells.get(bkey(b)), rung = rungOf(c), target = P.get(k).formula;
      const skip = new Set(lang.absorbed(rung).map(rk => rungAlias[rk]));
      const ex = b.filter(x => !skip.has(x));
      if (!ex.length) return null;
      const pool = lang.pool(target), insts = [];
      for (const e of ex) {
        const ax = P.get(e).formula, vs = [...vars(ax)].sort((a, b2) => a - b2);
        const choose = (i, s) => { if (i === vs.length) { insts.push([e, subst(ax, s)]); return; } for (const x of pool) choose(i + 1, { ...s, [vs[i]]: x }); };
        if (pool.length ** vs.length <= 4000) choose(0, {});
      }
      const deadline = Date.now() + budget;
      const found = (combo, by, depth) => ({ status: "instance", by, depth, instances: combo.map(([e, i]) => ({ of: e, formula: show(i) })) });
      if (lang.kind === "modal") {
        const d = mdepth(target) + 1;
        const prem = combo => combo.map(([, i]) => boxed(i, d)).reduce((acc, x) => acc === null ? x : AND(acc, x), null);
        for (const size of [1, 2, 3]) {
          if (size === 3 && insts.length > 60) break;
          const idx = [...Array(size).keys()];
          while (true) {
            if (Date.now() > deadline) return null;
            const combo = idx.map(i => insts[i]);
            if (isTheorem(C(prem(combo), target), "K")) return found(combo, "K", d);
            let j = size - 1;
            while (j >= 0 && idx[j] === insts.length - size + j) j--;
            if (j < 0) break;
            idx[j]++;
            for (let q = j + 1; q < size; q++) idx[q] = idx[q - 1] + 1;
          }
        }
        return null;
      }
      for (const x of insts) {
        if (Date.now() > deadline) return null;
        if (derivable([x[1]], target, rung)) return found([x], rung, 0);
      }
      for (let i = 0; i < insts.length; i++) for (let j = i + 1; j < insts.length; j++) {
        if (Date.now() > deadline) return null;
        if (derivable([insts[i][1], insts[j][1]], target, rung)) return found([insts[i], insts[j]], rung, 0);
      }
      return null;
    }
    const tried = new Set();
    const hardStop = t0 + (opts.totalBudgetMs ?? 20000);
    while (true) {
      if (decide() + chain()) continue;
      let changed = 0;
      for (const b of [...bases].sort((x, y) => x.length - y.length)) {
        if (Date.now() > hardStop) break;
        const c = cells.get(bkey(b));
        for (const k of keys) {
          if (c[k].status !== "unknown" || tried.has(bkey(b) + "|" + k)) continue;
          tried.add(bkey(b) + "|" + k);
          const hit = instance(b, k);
          if (hit) { c[k] = hit; changed++; }
        }
        if (changed) break;
      }
      if (!changed) break;
    }
    // 3. group into logics, order them
    const closure = new Map(bases.map(b => [bkey(b), new Set(visible.filter(k => proves(cells.get(bkey(b)), k)))]));
    const groups = [];
    for (const b of bases) {
      const g = groups.find(g => g[0].every(k => closure.get(bkey(b)).has(k)) && b.every(k => closure.get(bkey(g[0])).has(k)));
      if (g) g.push(b); else groups.push([b]);
    }
    const nodes = groups.map(g => {
      const rep = g.slice().sort((x, y) => x.length - y.length || bkey(x).localeCompare(bkey(y)))[0], c = cells.get(bkey(rep));
      // Degenerate logics: proving a bare letter means proving everything; □p everywhere is "Ver".
      const flag = proves(c, rungAlias.ALL) ? "inconsistent" : (rungAlias.VER && proves(c, rungAlias.VER)) ? "ver" : null;
      // Title: prefer presentations that don't use added principles, then ones that state the
      // structural rules the logic has (so the name says its floor), then the shortest.
      const fl = (lang.floorKeys || []).filter(k => closure.get(bkey(rep)).has(k));
      const miss = x => fl.filter(k => !x.includes(k)).length;
      const title = g.slice().sort((x, y) => (x.some(isCustom) - y.some(isCustom)) || miss(x) - miss(y) || describe(x).length - describe(y).length)[0];
      return { bases: g, rep, names: g.map(describe), title: describe(title), rung: rungOf(c), flag, proves: visible.filter(k => proves(c, k)),
               refutes: visible.filter(k => c[k].status === "refuted"), unknown: visible.filter(k => c[k].status === "unknown") };
    });
    const n = nodes.length;
    const le = (i, j) => nodes[i].rep.every(k => closure.get(bkey(nodes[j].rep)).has(k));
    const edges = [];
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      if (i === j || !le(i, j) || le(j, i)) continue;
      let cover = true;
      for (let k = 0; k < n && cover; k++) if (k !== i && k !== j && le(i, k) && le(k, j) && !le(k, i) && !le(j, k)) cover = false;
      if (!cover) continue;
      const lo = nodes[i].rep, hi = nodes[j].rep, clo = cells.get(bkey(lo));
      const witness = [...new Set([...hi, ...closure.get(bkey(hi))])].sort().find(k => clo[k].status === "refuted") ?? null;
      edges.push({ from: i, to: j, adds: hi.filter(k => !closure.get(bkey(lo)).has(k)).sort(), strict_by: witness, model: witness ? clo[witness].model : null });
    }
    // 4. package
    const used = new Set();
    for (const c of cells.values()) for (const k of keys) if (c[k].model !== undefined) used.add(c[k].model);
    const modelsOut = {};
    for (const i of used) modelsOut[i] = lang.kind === "modal" ? frameDict(ms[i]) : modelDict(ms[i]);
    const status = {};
    for (const c of cells.values()) for (const k of visible) status[c[k].status] = (status[c[k].status] || 0) + 1;
    return {
      kind: lang.kind, sandbox: true,
      principles: principles.map(p => ({ key: p.key, name: p.name, formula: show(p.formula), note: p.note || "", custom: !!p.custom,
                                         structural: !!p.structural, weakest: lang.weakest(p.formula) })),
      bases: bases.map(b => ({ axioms: b, name: describe(b), cells: Object.fromEntries(visible.map(k => [k, cells.get(bkey(b))[k]])) })),
      nodes, edges, models: modelsOut, status, ms: Date.now() - t0,
    };
  }

  /* Which of a set of assumptions are "baked in": provable from the others.
   * For each assumption x in `set`, the minimal subsets S of the other assumptions whose base
   * proves x (only subsets that are bases of `map` can be checked). Returns
   * { x: [{ from: [...keys], cell }] }; an empty list means x is needed. */
  function bakedIn(map, set) {
    const proving = st => ["given", "proved", "chained", "instance", "decided"].includes(st);
    const byKey = new Map(map.bases.map(b => [b.axioms.slice().sort().join("+"), b]));
    const out = {};
    for (const x of set) {
      const rest = set.filter(k => k !== x), found = [];
      const subsets = [];
      for (let mask = 0; mask < 1 << rest.length; mask++) subsets.push(rest.filter((_, i) => mask >> i & 1));
      subsets.sort((a, b) => a.length - b.length);
      for (const S of subsets) {
        if (found.some(f => f.from.every(k => S.includes(k)))) continue;         // keep only minimal witnesses
        const b = byKey.get(S.slice().sort().join("+"));
        if (b && b.cells[x] && proving(b.cells[x].status) && b.cells[x].status !== "given") found.push({ from: S, cell: b.cells[x] });
      }
      out[x] = found;
    }
    return out;
  }
  /** The bases needed to analyse a current set of assumptions: itself, each one-smaller set, each one-larger set. */
  function neighbourhood(set, catalog) {
    const out = [set];
    for (const x of set) out.push(set.filter(k => k !== x));
    for (const k of catalog) if (!set.includes(k)) out.push([...set, k]);
    // Every subset, so baked-in witnesses of any size can be found (sets are small).
    if (set.length <= 6) for (let mask = 0; mask < 1 << set.length; mask++) out.push(set.filter((_, i) => mask >> i & 1));
    return out;
  }

  const setStepLimit = n => { DERIVE_STEP_LIMIT = n; };
  const api = { compile, setStepLimit, bakedIn, neighbourhood, parse, parsePolish, show, key, vars, nvars, hasBox, canon, isTheorem, tautology, modalValid, s5Valid, godel,
                PROP, MODAL, computeMap, models, validity, holdsIn, frameValid, failingAssignment };
  root.Sandbox = api;
  if (typeof module !== "undefined" && module.exports) module.exports = api;
})(typeof window !== "undefined" ? window : globalThis);
