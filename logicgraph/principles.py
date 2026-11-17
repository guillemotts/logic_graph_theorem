"""Named logical principles in the implication-and-negation language, and base logics.

Minimal logic (Johansson) is axiomatized by ax-1, ax-2 and reductio. Every other
logic on the map is minimal logic plus some of the principles below. Formulas
are in Polish notation (C = implication, N = negation).
"""

from __future__ import annotations

from dataclasses import dataclass

from .formula import canon, parse_polish


@dataclass(frozen=True)
class Principle:
    key: str
    name: str
    polish: str
    note: str

    @property
    def formula(self):
        return canon(parse_polish(self.polish))


BASE = [
    Principle("K", "ax-1 (weakening)", "CpCqp", "a true statement follows from anything"),
    Principle("S", "ax-2 (distribution)", "CCpCqrCCpqCpr", "modus ponens under a hypothesis"),
    Principle("RED", "reductio", "CCpqCCpNqNp", "if p leads to both q and not-q, then not-p"),
]

# The principles whose relationships the map works out.
CATALOG = [
    Principle("EFQ", "explosion (ex falso)", "CNpCpq", "from a contradiction, anything follows"),
    Principle("DNE", "double-negation elimination", "CNNpp", "not-not-p gives p"),
    Principle("PEIRCE", "Peirce's law", "CCCpqpp", "classical, stated with implication only"),
    Principle("CM", "consequentia mirabilis", "CCNppp", "if not-p implies p, then p (Clavius)"),
    Principle("AX3", "ax-3 (Łukasiewicz contraposition)", "CCNpNqCqp", "the third axiom of the classical system used so far"),
    Principle("RAA", "classical reductio", "CCNpqCCNpNqp", "if not-p leads to a contradiction, then p"),
    Principle("CASES", "proof by cases on p", "CCpqCCNpqq", "excluded middle as a rule: q from p -> q and not-p -> q"),
    Principle("MEND", "Mendelson's third axiom", "CCNqNpCCNqpq", "another classical third axiom"),
    Principle("NNDNE", "double negation of DNE", "NNCNNpp", "intuitionistically valid, but not minimally"),
    Principle("NEGEFQ", "explosion into negations", "CNpCpNq", "a contradiction refutes anything"),
    Principle("TNE", "triple-negation elimination", "CNNNpNp", "valid in minimal logic"),
    Principle("CONTRA", "contraposition", "CCpqCNqNp", "valid in minimal logic"),
    Principle("DNI", "double-negation introduction", "CpNNp", "valid in minimal logic"),
]

BY_KEY = {p.key: p for p in BASE + CATALOG}

# Named logics, for labelling nodes of the map.
NAMED_LOGICS = {
    (): "minimal",
    ("EFQ",): "intuitionistic",
    ("DNE",): "classical",
}
