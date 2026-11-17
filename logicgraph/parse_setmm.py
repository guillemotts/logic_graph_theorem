"""Parse a Metamath database (set.mm) into a theorem dependency graph.

Outputs two CSV tables:

  nodes.csv  one row per `|-` assertion (axiom, definition or theorem)
  edges.csv  one row per (lemma, theorem) pair: `lemma` was used to prove `theorem`

Only assertions whose typecode is `|-` become nodes. Syntax statements
(`wff`, `class`, `setvar`, ...) and a proof's own hypotheses are filtered out,
as the README's "parsing shortcut" describes. Edges come straight from the
label list of each proof, so they record *which* lemmas a proof uses, not
*how many times*.

Usage:
    python -m logicgraph.parse_setmm data/raw/set.mm data/processed
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# A comment is `$(` ... `$)`, each delimited by whitespace.
COMMENT_RE = re.compile(r"(?<!\S)\$\((?!\S)(.*?)(?<!\S)\$\)(?!\S)", re.DOTALL)

# Section headers inside comments: a separator line, a title line, the same
# separator again. The separator's first two characters give the level.
HEADER_RE = re.compile(r"^([#*=.\-]{20,})[ \t]*\n[ \t]*(\S[^\n]*?)[ \t]*\n\1[ \t]*$", re.MULTILINE)
HEADER_LEVELS = {"##": 0, "#*": 1, "=-": 2, "-.": 3}
LEVEL_NAMES = ["part", "chapter", "section", "subsection"]

CONTRIB_RE = re.compile(r"\(Contributed\s+by\s+([^,()]+?),\s*(\d{1,2}-[A-Z][a-z]{2}-\d{4})\.?\s*\)")
MONTHS = {m: i for i, m in enumerate(
    "Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec".split(), start=1)}

ALT_OLD_RE = re.compile(r"(ALT|OLD)(lem)?\d*$")  # idALT, sylOLD, alexsubALTlem3
MATHBOX_PART_MARK = "MATHBOXES"


@dataclass
class Assertion:
    label: str
    keyword: str            # "$a" or "$p"
    typecode: str
    statement: str          # math symbols after the typecode
    order: int              # position among all assertions (file order = topological order)
    headers: list[str]
    mathbox: bool
    n_hyps: int             # number of $e hypotheses in scope (= mandatory)
    comment: str
    proof_format: str = ""  # "compressed", "uncompressed", "" for $a
    incomplete: bool = False
    uses: list[str] = field(default_factory=list)


def iso_date(d: str) -> str:
    day, mon, year = d.split("-")
    return f"{year}-{MONTHS.get(mon, 0):02d}-{int(day):02d}"


def node_kind(a: Assertion) -> str:
    if a.keyword == "$p":
        return "theorem"
    if a.label.startswith("ax-"):
        return "axiom"
    if a.label.startswith("df-"):
        return "definition"
    return "axiom_other"


def parse(text: str) -> list[Assertion]:
    headers = ["", "", "", ""]
    mathbox = False
    pending_comment = ""          # last non-header comment since the previous assertion
    hyp_scopes: list[list[str]] = [[]]   # active $e labels per ${ $} block
    assertions: dict[str, Assertion] = {}
    ordered: list[Assertion] = []

    # One token stream for the whole file. Comments become marker tokens
    # ("\x00" + index) because a comment may sit inside a statement.
    comments: list[str] = []
    tokens: list[str] = []
    for i, piece in enumerate(COMMENT_RE.split(text)):
        if i % 2 == 1:
            tokens.append(f"\x00{len(comments)}")
            comments.append(piece)
        else:
            tokens.extend(piece.split())

    def until(stop: str, start: int) -> tuple[list[str], int]:
        """Tokens from `start` up to `stop` (comments dropped), and the index of `stop`."""
        end = tokens.index(stop, start)
        return [t for t in tokens[start:end] if not t.startswith("\x00")], end

    j = 0
    n = len(tokens)
    label = None
    while j < n:
        tok = tokens[j]
        if tok.startswith("\x00"):
            piece = comments[int(tok[1:])]
            j += 1
            found = False
            for m in HEADER_RE.finditer(piece):
                level = HEADER_LEVELS.get(m.group(1)[:2])
                if level is None:
                    continue
                found = True
                headers[level] = m.group(2).strip()
                for deeper in range(level + 1, len(headers)):
                    headers[deeper] = ""
                if level == 0 and MATHBOX_PART_MARK in headers[0].upper():
                    mathbox = True
            if not found:
                pending_comment = piece
        elif tok == "${":
            hyp_scopes.append([])
            j += 1
        elif tok == "$}":
            hyp_scopes.pop()
            j += 1
        elif tok in ("$c", "$v", "$d"):
            j = tokens.index("$.", j) + 1
        elif tok == "$[":
            raise ValueError("File inclusion ($[ ... $]) is not supported")
        elif tok == "$f":
            j = tokens.index("$.", j) + 1
            label = None
        elif tok == "$e":
            j = tokens.index("$.", j) + 1
            hyp_scopes[-1].append(label)
            label = None
        elif tok in ("$a", "$p"):
            if label is None:
                raise ValueError(f"{tok} without a label near token {j}")
            stop = "$." if tok == "$a" else "$="
            math, end = until(stop, j + 1)
            a = Assertion(
                label=label, keyword=tok, typecode=math[0],
                statement=" ".join(math[1:]), order=len(ordered),
                headers=list(headers), mathbox=mathbox,
                n_hyps=sum(len(s) for s in hyp_scopes),
                comment=pending_comment,
            )
            pending_comment = ""
            if tok == "$p":
                proof, pend = until("$.", end + 1)
                if proof and proof[0] == "(":
                    a.proof_format = "compressed"
                    close = proof.index(")")
                    refs = proof[1:close]
                    a.incomplete = "?" in "".join(proof[close + 1:])
                else:
                    a.proof_format = "uncompressed"
                    refs = proof
                    a.incomplete = "?" in refs
                seen = set()
                for r in refs:
                    if r in seen:
                        continue
                    seen.add(r)
                    dep = assertions.get(r)
                    if dep is not None and dep.typecode == "|-":
                        a.uses.append(r)
                j = pend + 1
            else:
                j = end + 1
            assertions[label] = a
            ordered.append(a)
            label = None
        elif tok.startswith("$"):
            raise ValueError(f"Unexpected keyword {tok!r}")
        else:
            label = tok
            j += 1
    return ordered


def write_tables(assertions: list[Assertion], out_dir: Path) -> tuple[int, int]:
    out_dir.mkdir(parents=True, exist_ok=True)
    nodes = [a for a in assertions if a.typecode == "|-"]
    node_cols = [
        "label", "kind", "order", "statement", "n_symbols", "n_hyps",
        *LEVEL_NAMES, "mathbox", "alt_or_old", "discouraged_usage",
        "discouraged_proof", "contributor", "contributed", "proof_format",
        "incomplete", "n_uses",
    ]
    with open(out_dir / "nodes.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(node_cols)
        for a in nodes:
            c = CONTRIB_RE.search(a.comment)
            w.writerow([
                a.label, node_kind(a), a.order, a.statement,
                len(a.statement.split()), a.n_hyps, *a.headers,
                int(a.mathbox), int(bool(ALT_OLD_RE.search(a.label))),
                int("New usage is discouraged" in a.comment),
                int("Proof modification is discouraged" in a.comment),
                " ".join(c.group(1).split()) if c else "", iso_date(c.group(2)) if c else "",
                a.proof_format, int(a.incomplete), len(a.uses),
            ])
    n_edges = 0
    with open(out_dir / "edges.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["lemma", "theorem"])
        for a in nodes:
            for u in a.uses:
                w.writerow([u, a.label])
                n_edges += 1
    return len(nodes), n_edges


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("database", type=Path, help="path to set.mm")
    ap.add_argument("out_dir", type=Path, help="directory for nodes.csv and edges.csv")
    args = ap.parse_args(argv)
    assertions = parse(args.database.read_text(encoding="utf-8"))
    n_nodes, n_edges = write_tables(assertions, args.out_dir)
    print(f"{len(assertions)} assertions parsed; {n_nodes} |- nodes, {n_edges} edges -> {args.out_dir}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
