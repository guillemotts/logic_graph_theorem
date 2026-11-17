"""Propositional formulas, unification and condensed detachment.

A formula is a nested tuple:

    int        a variable (0, 1, 2, ...)
    (a, b)     the implication  a -> b
    (a,)       the negation     not a

Theorems are kept in *canonical form*: variables renumbered 0, 1, 2, ... in
order of first occurrence, so two theorems are the same exactly when their
tuples are equal.

Condensed detachment (Meredith's rule D): given a major premise `A -> B` and a
minor premise `C`, find the most general substitution that makes `A` and `C`
equal, and conclude `B` under that substitution. A "D-proof" is a string in
prefix notation such as `DD211`: `D` applies the rule to the two proofs that
follow it, and a digit names an axiom.
"""

from __future__ import annotations

import itertools
import re

Formula = "int | tuple"

# ------------------------------------------------------------------ unification

def _walk(t, s: dict):
    while isinstance(t, int) and t in s:
        t = s[t]
    return t


def _occurs(v: int, t, s: dict) -> bool:
    stack = [t]
    while stack:
        x = _walk(stack.pop(), s)
        if x == v:
            return True
        if not isinstance(x, int):
            stack.extend(x)
    return False


def unify(a, b) -> dict | None:
    """Most general unifier of two formulas (as a triangular substitution), or None."""
    s: dict = {}
    stack = [(a, b)]
    while stack:
        x, y = stack.pop()
        x, y = _walk(x, s), _walk(y, s)
        if x == y:
            continue
        if isinstance(x, int):
            if _occurs(x, y, s):
                return None
            s[x] = y
        elif isinstance(y, int):
            if _occurs(y, x, s):
                return None
            s[y] = x
        elif len(x) != len(y):
            return None
        else:
            stack.extend(zip(x, y))
    return s


def subst(t, s: dict):
    """Apply a triangular substitution fully."""
    t = _walk(t, s)
    return t if isinstance(t, int) else tuple(subst(x, s) for x in t)


def _shift(t, k: int):
    return t + k if isinstance(t, int) else tuple(_shift(x, k) for x in t)


def _canon(t, m: dict):
    if isinstance(t, int):
        if t not in m:
            m[t] = len(m)
        return m[t]
    return tuple(_canon(x, m) for x in t)


def canon(t):
    """Rename variables to 0, 1, 2, ... in order of first occurrence."""
    return _canon(t, {})


_APART = 1 << 20   # offset that keeps the minor premise's variables apart from the major's


def cd(major, minor):
    """Condensed detachment. Returns the canonical conclusion, or None if it does not apply."""
    if isinstance(major, int) or len(major) != 2:
        return None
    s = unify(major[0], _shift(minor, _APART))
    return None if s is None else canon(subst(major[1], s))


def subsumes(general, specific) -> bool:
    """True if `specific` is a substitution instance of `general` (one-way matching)."""
    m: dict = {}
    stack = [(general, specific)]
    while stack:
        g, x = stack.pop()
        if isinstance(g, int):
            if m.setdefault(g, x) != x:
                return False
        elif isinstance(x, int) or len(g) != len(x):
            return False
        else:
            stack.extend(zip(g, x))
    return True


# ------------------------------------------------------------------ measures

def size(t) -> int:
    """Number of symbols: variables plus connectives."""
    return 1 if isinstance(t, int) else 1 + sum(size(x) for x in t)


def variables(t) -> set[int]:
    if isinstance(t, int):
        return {t}
    out: set[int] = set()
    for x in t:
        out |= variables(x)
    return out


def evaluate(t, env: dict) -> bool:
    if isinstance(t, int):
        return env[t]
    if len(t) == 1:
        return not evaluate(t[0], env)
    return (not evaluate(t[0], env)) or evaluate(t[1], env)


def is_tautology(t) -> bool:
    vs = sorted(variables(t))
    return all(evaluate(t, dict(zip(vs, bits)))
               for bits in itertools.product((False, True), repeat=len(vs)))


# ------------------------------------------------------------------ notations

_LETTERS = "pqrstuvwxyzabcdefghijklmno"            # Polish and display variable names
_SETMM_VARS = ["ph", "ps", "ch", "th", "ta", "et", "ze", "si", "rh", "mu", "la", "ka"]


def to_polish(t) -> str:
    """Polish notation: C = implication, N = negation, e.g. CpCqp. Variables past 26 are [n]."""
    if isinstance(t, int):
        return _LETTERS[t] if t < len(_LETTERS) else f"[{t}]"
    if len(t) == 1:
        return "N" + to_polish(t[0])
    return "C" + to_polish(t[0]) + to_polish(t[1])


def parse_polish(s: str):
    pos = 0

    def read():
        nonlocal pos
        ch = s[pos]
        pos += 1
        if ch == "C":
            a = read()
            return (a, read())
        if ch == "N":
            return (read(),)
        if ch == "[":
            end = s.index("]", pos)
            v = int(s[pos:end])
            pos = end + 1
            return v
        return _LETTERS.index(ch)

    t = read()
    if pos != len(s):
        raise ValueError(f"trailing text in Polish formula {s!r}")
    return t


def to_str(t, top: bool = True) -> str:
    """Readable form: (p → q), ¬p. Outer parentheses are dropped."""
    if isinstance(t, int):
        return _LETTERS[t] if t < len(_LETTERS) else f"v{t}"
    if len(t) == 1:
        return "¬" + to_str(t[0], False)
    inner = f"{to_str(t[0], False)} → {to_str(t[1], False)}"
    return inner if top else f"({inner})"


def to_setmm(t) -> str:
    """set.mm ASCII, e.g. `( ph -> ( ps -> ph ) )`, so the visualizer can render it."""
    if isinstance(t, int):
        return _SETMM_VARS[t] if t < len(_SETMM_VARS) else f"v{t}"
    if len(t) == 1:
        return "-. " + to_setmm(t[0])
    return f"( {to_setmm(t[0])} -> {to_setmm(t[1])} )"


_TOKEN = re.compile(r"\(|\)|->|~|-\.|[A-Za-z][A-Za-z0-9]*")


def parse_infix(s: str):
    """Parse `((P -> Q) -> ~ R)` (pmproofs.txt) or `( ph -> -. ps )` (set.mm).

    Variable names are numbered in order of first occurrence.
    """
    tokens = _TOKEN.findall(s)
    if "".join(tokens) != re.sub(r"\s+", "", s):
        raise ValueError(f"cannot tokenize formula {s!r}")
    names: dict[str, int] = {}
    pos = 0

    def read():
        nonlocal pos
        tok = tokens[pos]
        pos += 1
        if tok in ("~", "-."):
            return (read(),)
        if tok == "(":
            a = read()
            if tokens[pos] != "->":
                raise ValueError(f"expected -> in {s!r}")
            pos += 1
            b = read()
            if tokens[pos] != ")":
                raise ValueError(f"expected ) in {s!r}")
            pos += 1
            return (a, b)
        if tok in (")", "->"):
            raise ValueError(f"unexpected {tok} in {s!r}")
        return names.setdefault(tok, len(names))

    t = read()
    if pos != len(tokens):
        raise ValueError(f"trailing text in formula {s!r}")
    return t


# ------------------------------------------------------------------ axioms and D-proofs

AXIOM_SETS = {
    # Lukasiewicz's P2 as used by Metamath (ax-1, ax-2, ax-3).
    "lukasiewicz": ["CpCqp", "CCpCqrCCpqCpr", "CCNpNqCqp"],
    # Implication only: ax-1 and ax-2 (positive implicational calculus).
    "implicational": ["CpCqp", "CCpCqrCCpqCpr"],
}


def axioms(spec: str) -> list:
    """Axioms from a named set or a comma-separated list of Polish formulas."""
    polish = AXIOM_SETS.get(spec) or spec.split(",")
    return [canon(parse_polish(p)) for p in polish]


def eval_dproof(proof: str, axs: list):
    """Conclusion of a D-proof such as `DD211` (digits are 1-based axiom numbers)."""
    stack: list = []
    for ch in reversed(proof):
        if ch == "D":
            major, minor = stack.pop(), stack.pop()
            c = cd(major, minor)
            if c is None:
                raise ValueError(f"detachment does not apply inside {proof[:40]!r}")
            stack.append(c)
        else:
            stack.append(axs[int(ch) - 1])
    if len(stack) != 1:
        raise ValueError(f"malformed D-proof {proof[:40]!r}")
    return stack[0]
