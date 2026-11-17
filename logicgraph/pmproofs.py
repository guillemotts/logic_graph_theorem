"""Read Metamath's pmproofs.txt: shortest known D-proofs of Principia Mathematica theorems.

Each entry has three parts, each ended by `;` and followed by a `!` comment:

    ((P v P) -> P); ! *1.2 Taut            the theorem as Principia states it
    ((~ P -> P) -> P); ! Result of proof   what the proof proves, in -> and ~ only
    DD2DD2D13D2DD2D1311; ! 19 steps        the proof (D = detach, 1/2/3 = ax-1/2/3)

The "result of proof" is the formula our generator can produce, so that is what
identifies a named theorem. Several Principia numbers can share one result
(*1.3 and *2.02 are both ax-1).

Usage:
    python -m logicgraph.pmproofs data/raw/pmproofs.txt data/pm/pm_theorems.csv
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from .formula import axioms, canon, eval_dproof, parse_infix, size, to_polish, to_str

URL = "https://us.metamath.org/mmsolitaire/pmproofs.txt"


@dataclass
class Entry:
    number: str        # "*2.08", "peirce", ...
    name: str          # "Id", "" if Principia gives none
    statement: str     # as printed in Principia (may use v, ^, <->)
    result: tuple      # canonical formula the proof proves
    proof: str
    steps: int


def parse(text: str) -> list[Entry]:
    # Everything up to the last line of dashes is a comment header.
    lines = text.splitlines()
    start = max(i for i, l in enumerate(lines) if re.fullmatch(r"-{20,}", l.strip())) + 1
    parts: list[tuple[str, str]] = []      # (text before ';', comment after '!')
    buf: list[str] = []
    for line in lines[start:]:
        if ";" in line:
            body, _, rest = line.partition(";")
            buf.append(body)
            parts.append((" ".join(" ".join(buf).split()), rest.partition("!")[2].strip()))
            buf = []
        else:
            buf.append(line)
    if len(parts) % 3:
        raise ValueError(f"expected groups of three parts, found {len(parts)}")
    entries = []
    for (stmt, label), (result, tag), (proof, steps) in zip(*[iter(parts)] * 3):
        if tag != "Result of proof" or not re.fullmatch(r"\d+ steps?", steps):
            raise ValueError(f"unexpected entry near {label!r}")
        words = label.split()
        name = words[1] if len(words) > 1 and not words[1].startswith("(") else ""
        entries.append(Entry(words[0], name, stmt, canon(parse_infix(result)),
                             proof.replace(" ", ""), int(steps.split()[0])))
    return entries


def verify(entries: list[Entry]) -> list[str]:
    """Replay every proof; return a list of problems (empty if all proofs check)."""
    axs = axioms("lukasiewicz")
    problems = []
    for e in entries:
        if len(e.proof) != e.steps:
            problems.append(f"{e.number}: proof has {len(e.proof)} steps, file says {e.steps}")
        got = eval_dproof(e.proof, axs)
        if got != e.result:
            problems.append(f"{e.number}: proof gives {to_str(got)}, file says {to_str(e.result)}")
    return problems


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source", type=Path, help="path to pmproofs.txt")
    ap.add_argument("out", type=Path, help="CSV to write")
    args = ap.parse_args(argv)
    entries = parse(args.source.read_text())
    problems = verify(entries)
    for p in problems:
        print("MISMATCH", p, file=sys.stderr)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["number", "name", "statement", "formula", "readable", "size", "steps", "proof"])
        for e in entries:
            w.writerow([e.number, e.name, e.statement, to_polish(e.result), to_str(e.result),
                        size(e.result), e.steps, e.proof])
    print(f"{len(entries)} entries, {len({e.result for e in entries})} distinct results, "
          f"{len(entries) - len(problems)} proofs verified -> {args.out}", file=sys.stderr)
    if problems:
        sys.exit(1)


if __name__ == "__main__":
    main()
