"""Modal formulas, Kripke frames, and decision procedures for K and S4.

Formulas are tagged tuples (kept separate from formula.py's propositional encoding):

    int            a variable (0, 1, ...)
    ("N", a)       ¬a
    ("C", a, b)    a -> b
    ("L", a)       □a   ("necessarily a")

◇a ("possibly a") is ¬□¬a. Polish notation follows Łukasiewicz: C, N, L (□),
M (◇), variables p, q, r, ...

Semantics. A Kripke frame is a set of worlds with an accessibility relation;
□a is true at a world when a is true at every world it can access. A formula is
*valid on a frame* when it is true at every world under every valuation. A
frame on which all axioms of a normal modal logic are valid validates every
theorem of that logic (frame validity is preserved by modus ponens,
necessitation and substitution), so a frame where the axioms hold and P fails
certifies that the logic does not prove P.

Decision procedures (tableaux on negation normal form, no horizon):
  K    any frames                      (terminates because modal depth drops)
  S4   reflexive, transitive frames    (ancestor-subset blocking)
"""

from __future__ import annotations

import itertools
import sys

import numpy as np

# ------------------------------------------------------------------ syntax

def neg(a):
    return ("N", a)


def imp(a, b):
    return ("C", a, b)


def box(a):
    return ("L", a)


def dia(a):
    return ("N", ("L", ("N", a)))


def conj(a, b):
    return ("N", ("C", a, ("N", b)))


def parse_polish(s: str):
    pos = 0

    def read():
        nonlocal pos
        ch = s[pos]
        pos += 1
        if ch == "C":
            a = read()
            return imp(a, read())
        if ch == "N":
            return neg(read())
        if ch == "L":
            return box(read())
        if ch == "M":
            return dia(read())
        return "pqrstuvw".index(ch)

    t = read()
    if pos != len(s):
        raise ValueError(f"trailing text in {s!r}")
    return t


def variables(t) -> set[int]:
    if isinstance(t, int):
        return {t}
    out: set[int] = set()
    for x in t[1:]:
        out |= variables(x)
    return out


def depth(t) -> int:
    """Modal depth: the deepest nesting of □."""
    if isinstance(t, int):
        return 0
    d = max(depth(x) for x in t[1:])
    return d + 1 if t[0] == "L" else d


def to_str(t, top: bool = True) -> str:
    if isinstance(t, int):
        return "pqrstuvw"[t] if t < 8 else f"v{t}"
    if t[0] == "N":
        a = t[1]
        if not isinstance(a, int) and a[0] == "L" and not isinstance(a[1], int) and a[1][0] == "N":
            return "◇" + to_str(a[1][1], False)
        if not isinstance(a, int) and a[0] == "C" and not isinstance(a[2], int) and a[2][0] == "N":
            inner = f"{to_str(a[1], False)} ∧ {to_str(a[2][1], False)}"
            return inner if top else f"({inner})"
        return "¬" + to_str(a, False)
    if t[0] == "L":
        return "□" + to_str(t[1], False)
    inner = f"{to_str(t[1], False)} → {to_str(t[2], False)}"
    return inner if top else f"({inner})"


def substitute(t, sub: dict):
    if isinstance(t, int):
        return sub.get(t, t)
    return (t[0],) + tuple(substitute(x, sub) for x in t[1:])


def from_propositional(t):
    """Convert formula.py's encoding (ints, (a,) = ¬, (a, b) = ->) to this one."""
    if isinstance(t, int):
        return t
    if len(t) == 1:
        return neg(from_propositional(t[0]))
    return imp(from_propositional(t[0]), from_propositional(t[1]))


def godel_translation(t):
    """Gödel–McKinsey–Tarski translation of a propositional formula (formula.py encoding).

    p -> □p,  ¬A -> □¬A*,  A -> B -> □(A* -> B*). A is an intuitionistic theorem
    exactly when its translation is an S4 theorem, and a classical theorem
    exactly when its translation is an S5 theorem.
    """
    if isinstance(t, int):
        return box(t)
    if len(t) == 1:
        return box(neg(godel_translation(t[0])))
    return box(imp(godel_translation(t[0]), godel_translation(t[1])))


# ------------------------------------------------------------------ tableaux

def nnf(t, positive: bool = True):
    """Negation normal form: ("v", i), ("nv", i), ("and", a, b), ("or", a, b), ("box", a), ("dia", a)."""
    if isinstance(t, int):
        return ("v", t) if positive else ("nv", t)
    if t[0] == "N":
        return nnf(t[1], not positive)
    if t[0] == "C":
        if positive:
            return ("or", nnf(t[1], False), nnf(t[2], True))
        return ("and", nnf(t[1], True), nnf(t[2], False))
    return ("box", nnf(t[1], True)) if positive else ("dia", nnf(t[1], False))


def _saturate(s: frozenset, reflexive: bool):
    """All propositionally saturated, non-contradictory expansions of s (branching on 'or')."""
    # Expanded formulas stay in the set (S4's loop check compares whole sets);
    # a marker ("x", f) records that f was expanded. In S4, "□a here gives a here"
    # is applied once per box.
    def clash(c) -> bool:
        return any(f[0] == "v" and ("nv", f[1]) in c for f in c)

    def pending(c, kinds):
        return next((f for f in c if f[0] in kinds and ("x", f) not in c
                     and (f[0] != "box" or reflexive)), None)

    stack = [s]
    while stack:
        cur = stack.pop()
        if clash(cur):
            continue                           # prune as soon as p and ¬p meet
        # Non-branching rules first (and, and the T rule), then branch on an "or".
        todo = pending(cur, ("and", "box")) or pending(cur, ("or",))
        if todo is None:
            yield frozenset(f for f in cur if f[0] != "x")
            continue
        done = cur | {("x", todo)}
        if todo[0] == "and":
            stack.append(done | {todo[1], todo[2]})
        elif todo[0] == "or":
            if todo[1] in cur or todo[2] in cur:
                stack.append(done)             # already satisfied: no need to branch
            else:
                stack.append(done | {todo[2]})
                stack.append(done | {todo[1]})
        else:                                  # T rule (S4): □a at a world gives a there
            stack.append(done | {todo[1]})


class KProver:
    def __init__(self):
        self.memo: dict = {}

    def sat(self, s: frozenset) -> bool:
        hit = self.memo.get(s)
        if hit is not None:
            return hit
        result = False
        for world in _saturate(s, reflexive=False):
            boxes = [f[1] for f in world if f[0] == "box"]
            if all(self.sat(frozenset([f[1], *boxes])) for f in world if f[0] == "dia"):
                result = True
                break
        self.memo[s] = result
        return result


class S4Prover:
    """S4 tableau with ancestor blocking.

    A result whose computation never used blocking does not depend on the path
    that led to it (it is the plain tableau's answer, sound both ways), so it is
    cached and reused; results that did use blocking are not cached.
    """

    def __init__(self):
        self.cache: dict = {}

    def sat(self, s: frozenset, ancestors: tuple = ()) -> bool:
        return self._sat(s, ancestors)[0]

    def _sat(self, s: frozenset, ancestors: tuple) -> tuple[bool, bool]:
        hit = self.cache.get(s)
        if hit is not None:
            return hit, False
        used_blocking = False
        for world in _saturate(s, reflexive=True):
            boxes = frozenset(f for f in world if f[0] == "box")
            ok = True
            for f in world:
                if f[0] != "dia" or f[1] in world:
                    continue                                   # reflexivity: already true here
                core = boxes | {f[1]}
                if any(core <= a for a in ancestors + (world,)):
                    used_blocking = True
                    continue                                   # blocked: an earlier world can serve
                result, blocked = self._sat(core, ancestors + (world,))
                used_blocking |= blocked
                if not result:
                    ok = False
                    break
            if ok:
                if not used_blocking:
                    self.cache[s] = True
                return True, used_blocking
        if not used_blocking:
            self.cache[s] = False
        return False, used_blocking


def is_valid(t, logic: str = "K") -> bool:
    """Is t a theorem of K or S4? (Valid on every frame / every reflexive transitive frame.)"""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 20000))
    try:
        s = frozenset([nnf(t, False)])
        if logic == "K":
            return not KProver().sat(s)
        if logic == "S4":
            return not S4Prover().sat(s)
        raise ValueError(logic)
    finally:
        sys.setrecursionlimit(old)


# ------------------------------------------------------------------ Kripke frames

def frames(max_worlds: int = 4) -> list[np.ndarray]:
    """Every accessibility relation on 1..max_worlds worlds, as (n, n) boolean matrices."""
    out = []
    for n in range(1, max_worlds + 1):
        for bits in range(1 << (n * n)):
            out.append(np.array([[bits >> (i * n + j) & 1 for j in range(n)] for i in range(n)], dtype=bool))
    return out


def _succ_masks(rels: np.ndarray) -> np.ndarray:
    """(F, n) uint: bitmask of the worlds each world can access."""
    n = rels.shape[1]
    weights = (1 << np.arange(n)).astype(np.uint16)
    return (rels.astype(np.uint16) * weights[None, None, :]).sum(axis=2).astype(np.uint16)


def truth_sets(t, rels: np.ndarray) -> np.ndarray:
    """For F frames of n worlds: (F, V) bitmasks of worlds where t is true, for every valuation.

    Valuations assign each variable a set of worlds; V = (2**n) ** k for k variables.
    """
    F, n, _ = rels.shape
    full = np.uint16((1 << n) - 1)
    k = max(variables(t)) + 1 if variables(t) else 0
    grid = np.indices((1 << n,) * k).reshape(k, -1).astype(np.uint16) if k else np.zeros((0, 1), np.uint16)
    succ = _succ_masks(rels)

    def ev(s):
        if isinstance(s, int):
            return np.broadcast_to(grid[s][None, :], (F, grid.shape[1]))
        if s[0] == "N":
            return ~ev(s[1]) & full
        if s[0] == "C":
            return (~ev(s[1]) | ev(s[2])) & full
        inner = ev(s[1])
        out = np.zeros_like(inner)
        for w in range(n):
            ok = (succ[:, w][:, None] & ~inner & full) == 0
            out |= ok.astype(np.uint16) << w
        return out

    return ev(t)


def frame_validity(formulas: list, rels_list: list[np.ndarray]) -> np.ndarray:
    """Boolean (len(frames), len(formulas)): is formula j valid on frame i?"""
    out = np.zeros((len(rels_list), len(formulas)), dtype=bool)
    by_n: dict[int, list[int]] = {}
    for i, r in enumerate(rels_list):
        by_n.setdefault(r.shape[0], []).append(i)
    for n, idx in by_n.items():
        rels = np.stack([rels_list[i] for i in idx])
        full = (1 << n) - 1
        for j, t in enumerate(formulas):
            out[idx, j] = (truth_sets(t, rels) == full).all(axis=1)
    return out


def failing_point(t, rel: np.ndarray) -> dict | None:
    """A valuation and world where t is false on this frame."""
    n = rel.shape[0]
    vals = truth_sets(t, rel[None])[0]
    k = max(variables(t)) + 1 if variables(t) else 0
    grid = np.indices((1 << n,) * k).reshape(k, -1) if k else np.zeros((0, 1), int)
    for col, v in enumerate(vals.tolist()):
        if v != (1 << n) - 1:
            world = next(w for w in range(n) if not v >> w & 1)
            return {"world": world, "valuation": {"pqrstuvw"[x]: [w for w in range(n) if grid[x, col] >> w & 1]
                                                  for x in range(k)}}
    return None


def frame_dict(rel: np.ndarray) -> dict:
    n = rel.shape[0]
    return {"worlds": n, "arrows": [[i, j] for i in range(n) for j in range(n) if rel[i, j]]}


# ------------------------------------------------------------------ S5 (for the bridge)

def s5_valid_small(t) -> bool:
    """S5 validity for formulas with at most 4 variables, by checking every cluster of valuations.

    An S5 model is, up to bisimulation, a nonempty set of propositional valuations
    that all see each other; there are 2**(2**k) - 1 of them for k variables.
    """
    k = max(variables(t)) + 1 if variables(t) else 0
    if k > 4:
        raise ValueError("too many variables for the cluster check")
    W = 1 << k                                   # one world per valuation
    clusters = np.arange(1, 1 << W, dtype=np.int64)            # bitmask of which valuations exist

    def ev(s):
        # (len(clusters), W) truth of s at each valuation-world (only meaningful where present)
        if isinstance(s, int):
            row = np.array([(w >> s) & 1 for w in range(W)], dtype=bool)
            return np.broadcast_to(row, (len(clusters), W))
        if s[0] == "N":
            return ~ev(s[1])
        if s[0] == "C":
            return ~ev(s[1]) | ev(s[2])
        inner = ev(s[1])
        present = ((clusters[:, None] >> np.arange(W)[None, :]) & 1).astype(bool)
        everywhere = (inner | ~present).all(axis=1)
        return np.broadcast_to(everywhere[:, None], (len(clusters), W))

    present = ((clusters[:, None] >> np.arange(W)[None, :]) & 1).astype(bool)
    return bool((ev(t) | ~present).all())
