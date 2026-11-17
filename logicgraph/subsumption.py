"""Find theorems that are just special cases of other theorems.

`p -> (p -> p)` is an instance of ax-1 `p -> (q -> p)`. Condensed detachment
needs a 13-step proof to produce exactly that instance, but nobody would count
it as a theorem of its own: anywhere it is used, ax-1 does the same job. A
theorem is *redundant* when another theorem that is at least as short to prove
subsumes it (has it as a substitution instance).

The index is a discrimination tree: theorems are stored by their preorder
symbol sequence with every variable written `*`. A lookup walks the query
formula and, wherever the tree has a `*`, skips a whole subformula. That
ignores whether repeated variables agree, so hits are confirmed with
`formula.subsumes`.
"""

from __future__ import annotations

from .formula import subsumes

_IDS = "ids"


def _tokens(t, out: list) -> list:
    if isinstance(t, int):
        out.append("*")
    else:
        out.append("N" if len(t) == 1 else "C")
        for x in t:
            _tokens(x, out)
    return out


class GeneralizationIndex:
    def __init__(self):
        self.root: dict = {}

    def add(self, key, t) -> None:
        node = self.root
        for tok in _tokens(t, []):
            node = node.setdefault(tok, {})
        node.setdefault(_IDS, []).append((key, t))

    def generalizations(self, t):
        """Yield (key, g) for every stored g that has t as an instance (including t itself)."""
        stack = [(self.root, (t,))]
        while stack:
            node, pending = stack.pop()
            if not pending:
                for key, g in node.get(_IDS, ()):
                    if subsumes(g, t):
                        yield key, g
                continue
            x, rest = pending[0], pending[1:]
            star = node.get("*")
            if star is not None:
                stack.append((star, rest))          # a variable of g swallows all of x
            if not isinstance(x, int):
                child = node.get("N" if len(x) == 1 else "C")
                if child is not None:
                    stack.append((child, x + rest))
        return


def redundant(formulas: list, steps: list[int]) -> list[int | None]:
    """For each theorem, the id of a strictly more general theorem that is no longer to prove, or None.

    When several qualify, the one with the shortest proof (then the lowest id) is returned.
    """
    index = GeneralizationIndex()
    for i, t in enumerate(formulas):
        index.add(i, t)
    out: list[int | None] = []
    for i, t in enumerate(formulas):
        best = None
        for j, _ in index.generalizations(t):
            if j != i and steps[j] <= steps[i] and (best is None or (steps[j], j) < (steps[best], best)):
                best = j
        out.append(best)
    return out
