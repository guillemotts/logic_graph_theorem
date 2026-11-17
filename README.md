# The Logic Map

**An interactive map of logics, and of the assumptions that separate them.**

**[Open the map →](https://guillemotts.github.io/logic_graph_theorem/)**

Every logic rests on assumptions that are simply taken as given: an unused assumption does no harm (weakening), an assumption may be used twice (contraction), from a contradiction anything follows (explosion), every statement is true or false (excluded middle), and so on. Each dot on the map is a logic, and each line is one assumption added. Break an assumption and watch which logic you land in; add one and see which other assumptions it quietly "bakes in".

Every relationship on the map is certified. A line exists because a proof was found, and two logics are kept apart because a small truth table (or, for modal logic, a small Kripke frame) shows one statement holding in one logic and failing in the other.

## Things to try

- **Drop weakening** from intuitionistic logic. You land in a relevant logic, and distribution goes too: it needs both structural rules.
- **Add Peirce's law** `((p → q) → p) → p` to linear logic. On its face it's about implication only, yet it brings in weakening and contraction too: it bakes in both structural rules.
- **Switch to Modal** for the modal cube (K, T, S4, S5, GL, …). Start from KD and add T, and D becomes baked in, because T proves it.
- **Open Discoveries.** A search tried every small formula as a new assumption. It found single formulas that smuggle in several principles at once, logics that sit between the ones on the map, and some known logics it rediscovered without being told (the mingle axiom, 3-valued Gödel logic).

## A few findings

| Starting logic | Add | Result |
|---|---|---|
| linear | Peirce's law | Weakening and contraction come with it. |
| linear | `(p ∧ (p → q)) → q` (modus ponens as one formula) | Exactly contraction + non-contradiction. |
| linear | `p → ((q ∨ ¬p) → q)` (disjunctive syllogism) | Exactly weakening + explosion. |
| linear | excluded middle + explosion | Contraction, by proof by cases. Excluded middle alone doesn't give it. |
| affine | double negation | Explosion. Without weakening it doesn't. |
| intuitionistic | `p ∨ ((p → q) ∨ ¬q)` | A logic between Gödel–Dummett and classical (3-valued Gödel logic). |

Whether a finding is new to the literature is a separate question: the engine certifies facts but doesn't know which are already known.

## Run it locally

The map is a static page. Everything runs in the browser.

```bash
python3 -m http.server 8765 --directory viz
```

Then open <http://localhost:8765>.

Tests (Python 3 with `numpy`, `scipy`, `networkx` and `scikit-learn`, plus Node for the browser engine):

```bash
python3 -m unittest discover tests
```

Rerun the formula search (takes about 2 hours; results are already in `data/discoveries.json`):

```bash
node scripts/discover.js
```

## What's in the repo

| Path | What it is |
|---|---|
| `viz/index.html` | The logic map page. |
| `viz/sandbox.js` | The engine: parser, proof search for each logic, countermodels, map building. |
| `viz/discover.js`, `scripts/discover.js` | The formula search behind Discoveries. |
| `logicgraph/` | The Python side: the earlier theorem-graph work and the original logic maps. |
| `data/` | Small committed results. Large downloads and generated files are in `.gitignore`; `docs/NOTES.md` has the commands to rebuild them. |
| `tests/` | Python tests, some of which drive the JavaScript engine through Node. |
| `docs/NOTES.md` | The full lab notebook. |

## How the project got here

It started as a graph of theorems, where an edge means "was used to prove". The first version used Metamath's `set.mm` library, and the second a generator of every short proof from three axioms. Graph algorithms on that graph ranked which theorems are load-bearing. The more interesting question turned out to be one level up: which *assumptions* are load-bearing, and how logics relate to each other when you add or remove them. That became the map. Every step, with results and caveats, is in [docs/NOTES.md](docs/NOTES.md).
