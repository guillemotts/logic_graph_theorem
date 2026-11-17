"""Countermodels: small many-valued truth tables that certify "P does not follow".

A *matrix* has truth values 0..n-1, a table for `->`, a table for `¬`, and a
set of *designated* ("true enough") values. It is a model of a logic when every
axiom of the logic always comes out designated and modus ponens preserves
designation (a designated and a -> b designated imply b designated). Then every
theorem of the logic, at any proof length, comes out designated. So if
principle P fails in a model of B, B can never prove P.

Two families are searched:

  heyting   Finite Heyting algebras (the down-set lattices of posets with up to
            4 points, up to 16 values), designated = top, `->` the Heyting
            implication, `¬a = a -> f` for every choice of the element f.
            With f = bottom these are models of intuitionistic logic; with any f
            they are models of minimal logic (⊥ is just an atom there).
  all3      Every 2- and 3-valued matrix (every `->` table, `¬` table and
            designated set), filtered to those where ax-1 and ax-2 hold and
            modus ponens preserves designation.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

import numpy as np

from .formula import to_str, variables


@dataclass
class Matrix:
    name: str
    imp: np.ndarray        # (n, n) int: imp[a, b] = a -> b
    neg: np.ndarray        # (n,) int
    designated: frozenset
    labels: list[str]      # display names of the values

    @property
    def n(self) -> int:
        return len(self.neg)

    def to_dict(self) -> dict:
        return {"name": self.name, "values": self.labels, "designated": sorted(self.designated),
                "imp": self.imp.tolist(), "neg": self.neg.tolist()}


# ------------------------------------------------------------------ evaluation

def _assignments(n: int, k: int) -> np.ndarray:
    """(k, n**k) array: every assignment of k variables."""
    if k == 0:
        return np.zeros((0, 1), dtype=np.int64)
    grid = np.indices((n,) * k).reshape(k, -1)
    return grid.astype(np.int64)


def evaluate_batch(t, imps: np.ndarray, negs: np.ndarray) -> np.ndarray:
    """Values of t under every assignment, for T matrices of the same size at once.

    imps: (T, n, n), negs: (T, n). Returns (T, n**k) where k = number of variables.
    Variables must be numbered 0..k-1 (canonical form).
    """
    T, n = negs.shape
    k = max(variables(t)) + 1
    asg = _assignments(n, k)
    flat = imps.reshape(T, n * n)

    def ev(s):
        if isinstance(s, int):
            return np.broadcast_to(asg[s], (T, asg.shape[1]))
        if len(s) == 1:
            return np.take_along_axis(negs, ev(s[0]), axis=1)
        a, b = ev(s[0]), ev(s[1])
        return np.take_along_axis(flat, a * n + b, axis=1)

    return ev(t)


def holds(t, m: Matrix) -> bool:
    vals = evaluate_batch(t, m.imp[None], m.neg[None])[0]
    des = np.zeros(m.n, dtype=bool)
    des[list(m.designated)] = True
    return bool(des[vals].all())


def failing_assignment(t, m: Matrix) -> dict | None:
    """One assignment of values to variables under which t is not designated."""
    vals = evaluate_batch(t, m.imp[None], m.neg[None])[0]
    k = max(variables(t)) + 1
    asg = _assignments(m.n, k)
    for col in range(vals.shape[0]):
        if vals[col] not in m.designated:
            return {to_str(v): m.labels[int(asg[v, col])] for v in range(k)}
    return None


def mp_closed(m: Matrix) -> bool:
    return all(b in m.designated for a in m.designated for b in range(m.n) if m.imp[a, b] in m.designated)


# ------------------------------------------------------------------ Heyting algebras

def _posets(size: int):
    """All partial orders on {0..size-1} as boolean matrices le[i, j] = i <= j (with duplicates)."""
    pairs = [(i, j) for i in range(size) for j in range(size) if i != j]
    seen = set()
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        le = np.eye(size, dtype=bool)
        for (i, j), bit in zip(pairs, bits):
            le[i, j] = bool(bit)
        if any(le[i, j] and le[j, i] for i, j in pairs):
            continue
        if not all(le[i, k] for i in range(size) for j in range(size) for k in range(size) if le[i, j] and le[j, k]):
            continue
        key = le.tobytes()
        if key not in seen:
            seen.add(key)
            yield le


def _downset_algebra(le: np.ndarray) -> tuple[np.ndarray, list[int]]:
    """Heyting implication table of the lattice of down-sets of a poset; elements are bitmasks."""
    size = le.shape[0]
    below = [sum(1 << j for j in range(size) if le[j, i]) for i in range(size)]
    elems = [m for m in range(1 << size) if all(not (m >> i & 1) or (below[i] & ~m) == 0 for i in range(size))]
    elems.sort(key=lambda m: (bin(m).count("1"), m))
    index = {m: k for k, m in enumerate(elems)}
    n = len(elems)
    imp = np.zeros((n, n), dtype=np.int64)
    for a, ma in enumerate(elems):
        for b, mb in enumerate(elems):
            # a -> b = { x : every y <= x in a is in b }
            mc = sum(1 << x for x in range(size) if (below[x] & ma & ~mb) == 0)
            imp[a, b] = index[mc]
    return imp, elems


def heyting_models(max_points: int = 4) -> list[Matrix]:
    out, seen = [], set()
    for size in range(1, max_points + 1):
        for le in _posets(size):
            imp, elems = _downset_algebra(le)
            n = len(elems)
            key = (n, imp.tobytes())
            if key in seen:
                continue
            seen.add(key)
            top = n - 1
            labels = ["0"] + [f"a{k}" for k in range(1, n - 1)] + ["1"] if n > 2 else ["0", "1"]
            for f in range(n):
                neg = imp[:, f].copy()
                kind = "Boolean" if n == 2 else f"Heyting({n})"
                fname = "⊥=0" if f == 0 else ("⊥=1" if f == top else f"⊥={labels[f]}")
                out.append(Matrix(f"{kind}, {fname}", imp, neg, frozenset({top}), labels))
    return out


# ------------------------------------------------------------------ all small matrices

K = (0, (1, 0))
S = ((0, (1, 2)), ((0, 1), (0, 2)))


def small_models(n: int) -> list[Matrix]:
    """Every n-valued matrix (n <= 3) where ax-1, ax-2 hold and modus ponens preserves designation."""
    tables = np.array(list(itertools.product(range(n), repeat=n * n)), dtype=np.int64).reshape(-1, n, n)
    zero_neg = np.zeros((len(tables), n), dtype=np.int64)
    k_vals = evaluate_batch(K, tables, zero_neg)
    s_vals = evaluate_batch(S, tables, zero_neg)
    out = []
    for size in range(1, n):
        for des in itertools.combinations(range(n), size):
            dmask = np.zeros(n, dtype=bool)
            dmask[list(des)] = True
            ok = dmask[k_vals].all(axis=1) & dmask[s_vals].all(axis=1)
            for t in np.flatnonzero(ok).tolist():
                imp = tables[t]
                if not all(b in des for a in des for b in range(n) if imp[a, b] in des):
                    continue
                for neg in itertools.product(range(n), repeat=n):
                    labels = [str(v) for v in range(n)]
                    out.append(Matrix(f"{n}-valued #{t}", imp, np.array(neg, dtype=np.int64),
                                      frozenset(des), labels))
    return out


def all_models(max_points: int = 4, max_values: int = 3) -> list[Matrix]:
    """Heyting models first (they are easier to read), then all small matrices."""
    models = heyting_models(max_points)
    for n in range(2, max_values + 1):
        models += small_models(n)
    return models


def validity_table(formulas: list, models: list[Matrix]) -> np.ndarray:
    """Boolean (len(models), len(formulas)) table: does formula j hold in model i?"""
    out = np.zeros((len(models), len(formulas)), dtype=bool)
    by_size: dict[int, list[int]] = {}
    for i, m in enumerate(models):
        by_size.setdefault(m.n, []).append(i)
    for n, idx in by_size.items():
        imps = np.stack([models[i].imp for i in idx])
        negs = np.stack([models[i].neg for i in idx])
        des = np.zeros((len(idx), n), dtype=bool)
        for r, i in enumerate(idx):
            des[r, list(models[i].designated)] = True
        for j, t in enumerate(formulas):
            vals = evaluate_batch(t, imps, negs)
            out[idx, j] = np.take_along_axis(des, vals, axis=1).all(axis=1)
    return out
