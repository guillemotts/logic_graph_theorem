"""Decide whether a formula is a theorem of minimal or intuitionistic logic.

Negation is read as implication into falsum: `¬A` is `A -> ⊥`.

  intuitionistic  ⊥ proves anything (explosion).
  minimal         ⊥ is an ordinary atom with no special rule (Johansson 1937).
  classical       truth tables (`formula.is_tautology`).

The procedure is Dyckhoff's contraction-free sequent calculus G4ip (LJT,
1992), restricted to implication and ⊥. Every rule makes the sequent smaller,
so proof search always terminates, with no horizon: a "no" here means "not a
theorem of this logic", full stop.

Rules, for a sequent  Γ ⊢ G :
  axiom      G is an atom in Γ
  ⊥L         ⊥ in Γ                                          (intuitionistic only)
  →R         Γ ⊢ A -> B   from  Γ, A ⊢ B                       (invertible)
  p→L        Γ, p, p -> B ⊢ G   from  Γ, p, B ⊢ G               (invertible, p an atom)
  →→L        Γ, (C -> D) -> B ⊢ G   from  Γ, D -> B, C ⊢ D  and  Γ, B ⊢ G
"""

from __future__ import annotations

import sys

BOT = -1        # falsum; ordinary variables are 0, 1, 2, ...


def to_implicational(t):
    """Rewrite ¬A as A -> ⊥."""
    if isinstance(t, int):
        return t
    if len(t) == 1:
        return (to_implicational(t[0]), BOT)
    return (to_implicational(t[0]), to_implicational(t[1]))


class Prover:
    def __init__(self, explosion: bool):
        self.explosion = explosion
        self.memo: dict = {}

    def prove(self, gamma: frozenset, goal) -> bool:
        key = (gamma, goal)
        hit = self.memo.get(key)
        if hit is not None:
            return hit
        self.memo[key] = False          # guards against re-entry; G4ip itself never loops
        result = self._prove(gamma, goal)
        self.memo[key] = result
        return result

    def _prove(self, gamma: frozenset, goal) -> bool:
        # →R is invertible: always apply it first.
        while not isinstance(goal, int):
            gamma = gamma | {goal[0]}
            goal = goal[1]
        # Saturate with the invertible left rules.
        g = set(gamma)
        changed = True
        while changed:
            changed = False
            if self.explosion and BOT in g:
                return True
            for f in list(g):
                if isinstance(f, int):
                    continue
                a, b = f
                if self.explosion and a == BOT:          # ⊥ -> B is useless in intuitionistic logic
                    g.discard(f)
                    changed = True
                elif isinstance(a, int) and a in g:      # p -> B with p available: replace by B
                    g.discard(f)
                    g.add(b)
                    changed = True
        if goal in g:
            return True
        gamma = frozenset(g)
        # The one non-invertible rule: (C -> D) -> B on the left.
        for f in gamma:
            if isinstance(f, int) or isinstance(f[0], int):
                continue
            (c, d), b = f
            rest = gamma - {f}
            if self.prove(rest | {(d, b), c}, d) and self.prove(rest | {b}, goal):
                return True
        return False


def is_theorem(t, logic: str) -> bool:
    """`logic` is "minimal", "intuitionistic" or "classical". `t` uses the formula.py encoding."""
    if logic == "classical":
        from .formula import is_tautology
        return is_tautology(t)
    if logic not in ("minimal", "intuitionistic"):
        raise ValueError(logic)
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 10000))
    try:
        return Prover(explosion=(logic == "intuitionistic")).prove(frozenset(), to_implicational(t))
    finally:
        sys.setrecursionlimit(old)


def weakest_logic(t) -> str:
    """The weakest of minimal ⊂ intuitionistic ⊂ classical that proves t ("none" if not a tautology)."""
    for logic in ("minimal", "intuitionistic", "classical"):
        if is_theorem(t, logic):
            return logic
    return "none"
