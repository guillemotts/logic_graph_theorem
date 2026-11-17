# Logic Graph Project: lab notebook

> The full record of how this project developed, section by section. For the short version, see the [README](../README.md).

> **TL;DR:** Build a graph where every node is a logic theorem and every edge means "was used to prove." Then use graph algorithms to measure *which theorems matter and why*. The graph algorithms are the main contribution.

---

## 1. The idea in one paragraph

Start from a few axioms. Make new theorems by "plugging" existing theorems into each other. Record every plug-in as edges in a graph. Then run graph algorithms over the result to find theorems that are load-bearing, unavoidable, compressive, bridging, or deep, and to see exactly what a given assumption (axiom) buys you.

---

## 2. Background (the basics)

A logic system has three ingredients:

- **Formulas**: strings like $\varphi \to \psi$ ("if $\varphi$ then $\psi$").
- **Axioms**: formulas accepted without proof. These are the root nodes.
- **Rules**: ways to make new theorems. The main one is **modus ponens**: from $\varphi$ and $\varphi \to \psi$, conclude $\psi$.

Example axioms (Łukasiewicz system, implication part):

$$\text{A1:}\quad \varphi \to (\psi \to \varphi)$$

$$\text{A2:}\quad \bigl(\varphi \to (\psi \to \chi)\bigr) \to \bigl((\varphi \to \psi) \to (\varphi \to \chi)\bigr)$$

The Greek letters are slots: any formula can be substituted into them.

### Worked example: proving $\varphi \to \varphi$

1. A2 with $\psi := (\varphi \to \varphi)$, $\chi := \varphi$: $\bigl(\varphi \to ((\varphi \to \varphi) \to \varphi)\bigr) \to \bigl((\varphi \to (\varphi \to \varphi)) \to (\varphi \to \varphi)\bigr)$
2. A1 with $\psi := (\varphi \to \varphi)$: $\varphi \to ((\varphi \to \varphi) \to \varphi)$
3. Modus ponens on 2 and 1: $(\varphi \to (\varphi \to \varphi)) \to (\varphi \to \varphi)$
4. A1 with $\psi := \varphi$: $\varphi \to (\varphi \to \varphi)$
5. Modus ponens on 4 and 3: $\varphi \to \varphi$

### The "plug in" operation has a name

**Condensed detachment** (C. A. Meredith): take two theorems, find the most general substitution that makes one match the left side of the other (this is called *unification*), then apply modus ponens. It is the engine for automatically growing the graph.

---

## 3. Graph structure (design decisions)

- **Hypergraph, not a plain graph.** Modus ponens needs *two* parents at once. Model it with an intermediate "proof step" node that both parents point into.
- **Many proofs per theorem.** Either keep only the shortest proof, or keep all of them (an AND-OR graph). Keeping all of them makes dependency questions richer.
- **One component, not many.** Everything descends from the axioms, so "bridging connected components" doesn't work literally. Instead, **tag each theorem with the set of axioms its proof uses.** "What does axiom $X$ buy you?" then means: which theorems appear only once $X$ is added.
  - Example: adding **Peirce's law** $((\varphi \to \psi) \to \varphi) \to \varphi$ unlocks classical-only theorems such as $\neg\neg\varphi \to \varphi$.
  - **Caveat:** "search didn't find a proof without $X$" is not the same as "no proof exists." To *certify* that $X$ is needed, find a **countermodel**: a many-valued truth table where every other axiom holds but the theorem fails.

---

## 4. The core contribution: kinds of "importance"

Each kind of importance gets its own algorithm, and each one gives a different intuition.

| Kind | Question | Method |
|---|---|---|
| 🧱 **Load-bearing** | What breaks if I remove it? | Knockout analysis |
| 🚪 **Unavoidable** | Does every road go through it? | Dominator trees |
| 🗜️ **Compressive** | Does naming it save the most work? | Proof-length savings |
| 🌉 **Bridging** | Does it connect two regions? | Community detection + inter-community edges |
| 🤯 **Deep** | Is it short to state but hard to prove? | Proof length ÷ statement size |
| 🌱 **Generative** | Does it open new territory? | Count of genuinely new (non-subsumed) children |

### Formulas

Let $L_G(t)$ be the shortest proof length of theorem $t$ in graph $G$, and $|t|$ the size of $t$'s statement in symbols.

**Load-bearing:** delete lemma $v$ and measure how much longer proofs get in total.

$$\Delta(v) = \sum_{t} \bigl( L_{G \setminus v}(t) - L_G(t) \bigr)$$

**Unavoidable:** $v$ *dominates* $t$ if every proof path from the axioms to $t$ passes through $v$.

**Compressive:**

$$\operatorname{gain}(v) = \bigl(\text{total steps saved across all proofs that use } v\bigr) - \bigl(\text{cost of proving } v \text{ once}\bigr)$$

**Deep:**

$$\operatorname{depth}(t) = \frac{L(t)}{|t|}$$

---

## 5. Pitfall: measuring the search instead of the math

On a brute-forced graph, a theorem can look central only because it is:

- **short**, so it unifies with many things,
- **found early**, so it had more rounds to collect children, or
- **picked by the search** among many possible proofs.

**Fix:** compare every score against a **baseline / null model** (e.g., rebuild with a shuffled search order or different proof choices). A lemma is interesting only if it beats what its size and age alone would predict.

---

## 6. Validation

Use a real formal library where humans have already chosen what matters.

- **Metamath `set.mm`**: tens of thousands of theorems with full proof dependencies.
- **Test:** do the scores rank famous, heavily reused theorems near the top?
- **Interesting output:** theorems scored highly that humans *didn't* bother to name. Those are the candidate findings.

---

## 7. Plan

The project now has two tracks.

### Track A: set.mm (frozen)
Graph algorithms on Metamath's human-written library. Built and working (sections 11–12), kept as a side dataset. It showed that with one proof per theorem the "what breaks" scores are degenerate, and that Metamath's proof conventions dominate naive scores. No further math-library scores are planned.

### Track B: generated propositional logic (active)
Our own exhaustive condensed-detachment generator for propositional logic, where every theorem can have many derivations. Built and validated against human-named theorems (section 13).

- Scope: implication and negation, Łukasiewicz axioms ax-1, ax-2, ax-3.
- Pipeline: condensed detachment → canonical variable names → every derivation recorded → redundant instances marked.
- **Sanity checks (all passing):** every generated theorem is a tautology; it finds $\varphi \to \varphi$ with the 5-step proof above; shortest proof lengths match the published ones.
- **First claim tested:** lemma discovery (does "naming this theorem shortens other proofs" pick out the theorems humans named?).

---

## 8. Two-day slice (realistic scope)

The full plan is weeks of work, and the condensed-detachment search is a whole project by itself. In two days, aim for:

1. **Parse `set.mm`** and build the dependency graph.
2. **Compute one score**, e.g. "deep."
3. **Run one check:** does the "deep" score rank Metamath's proofs from the **100 famous theorems** list higher than a simple baseline (citation count = in-degree)?

### Parsing shortcut

In `set.mm`'s **compressed proofs**, the labels a proof uses are listed in parentheses at the start:

```
thmname $p |- ... $= ( label1 label2 ... ) COMPRESSEDSTRING $.
```

So you can read the edges straight off without decompressing anything.

- **Filter out syntax labels** like `wi` and `wn`. The robust way is to keep only labels whose statement starts with the typecode `|-` (real theorems/axioms); `wff`, `class`, and `setvar` statements are syntax.
- A theorem's own mandatory hypotheses are implicit and don't appear in the list.
- A few proofs may be uncompressed; for those, every proof token is a label, so apply the same filter.
- This gives *which* lemmas a proof uses, not *how many times*. That's enough for in-degree and dominators; proof-length scores need either proof step counts or full decompression later.

---

## 9. Prior art

- **Metamath (`set.mm`)**: the closest existing graph; usable as data.
- **Lean's mathlib**: its dependency graph has been visualized; a picture of a mature version of this.
- **Saturation provers (Prover9, E)**: the same "generate everything, prune hard" loop.
- **DreamCoder**: source of the "learn which lemmas to name via compression" idea (for programs).

---

## 10. Open questions

- [x] Main goal: **lemma discovery** first. "What each axiom buys" and "importance across axiom systems" come after.
- [x] Which logic: **propositional**, generated by us.
- [x] Which importance score first: **compressive (naming gain)**. It is the one that survived the null model (section 13).
- [ ] How to get more ground truth. Only 14 human-named theorems fall inside a 21-step horizon.
- [ ] Is tree size the right cost? Proofs that share lemmas (DAG size) may rank things differently.
- [ ] Does importance survive a change of axiom system (Meredith's single axiom, others)?
- [x] How do different logics relate? Mapped for principles in implication and negation over minimal logic (section 14).
- [ ] Add "and" / "or" as primitive connectives, so excluded middle and De Morgan laws can join the map.
- [x] Extend the map to modal logic (section 15).
- [x] Let people add and remove assumptions and see what changes (section 16).

---

## 11. Running the code (Phase 1)

Python 3.10+. Steps 1–3 and 5 use only the standard library; step 4 needs `networkx`, `numpy`, `scipy` and `scikit-learn`.

```bash
# 1. Get the data (~52 MB)
curl -L -o data/raw/set.mm https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm

# 2. Parse into data/processed/{nodes,edges}.csv   (~2 s)
python3 -m logicgraph.parse_setmm data/raw/set.mm data/processed

# 3. Structural scores -> data/processed/scores.csv  (~3 s)
python3 -m logicgraph.scores data/processed

# 4. Graph algorithms -> data/processed/algo_*.csv etc.  (~30 s, needs networkx, numpy, scipy, scikit-learn)
python3 -m logicgraph.algorithms data/processed

# 5. Export for the visualizer -> viz/data.js
python3 -m logicgraph.export_viz data/processed viz/data.js
python3 -m logicgraph.export_viz data/processed viz/data.js

# 6. Open the visualizer
python3 -m http.server 8765 --directory viz   # then visit http://localhost:8765/explorer.html
```

| File | Contents |
|---|---|
| `nodes.csv` | One row per `\|-` statement: kind (axiom / definition / theorem), statement, part › chapter › section › subsection, mathbox flag, ALT/OLD and "discouraged" flags, contributor and date, number of hypotheses. `order` is file order, which is a topological order. |
| `edges.csv` | `lemma,theorem`: the lemma appears in the theorem's proof. Deduplicated (no multiplicities yet). |
| `scores.csv` | `in_degree`, `out_degree`, `reach` (transitive dependents), `n_ancestors`, `depth` (longest chain), axioms used. |

**Visualizer** (`viz/explorer.html`; the front page `viz/index.html` is now the logic map, section 17): *Explorer* shows a theorem's lemmas and citers (1 or 2 hops) with a details panel, including its graph-algorithm scores and an option to dim nodes outside its community. *Overview* has the percolation chart, the communities table, a chapter-to-chapter citation heatmap and a leaderboard over every score. Press `/` to search; URLs like `#fta` link to a theorem.

The set.mm numbers in sections 11–12 come from the copy downloaded on 2026-11-09 (49,923 `|-` statements). set.mm changes daily, so a fresh download will shift the counts.

**Known caveats**
- Edges record *which* lemmas a proof uses, not how often; proof-length scores need decompression (next step).
- set.mm states some derived results as `$a` axioms for convenience (e.g. `ax-ac2`, the `ax-cnex`… complex-number axioms), so "axioms used" lists those names rather than the minimal ZFC base.
- Mathboxes are 17.7k of the 49.9k statements and are less curated; filter them with the `mathbox` column.

---

## 12. Graph algorithms (`logicgraph/algorithms.py`)

Run on the **main library** (31.8k statements, 543k citations; mathboxes and ALT/OLD proofs dropped).

| Output | Algorithm | Question |
|---|---|---|
| `algo_nodes.csv` → `art_cut`, `algo_bridges.csv` | Tarjan low-link (undirected cut vertices and bridges, with the size of what splits off) | Which single node or edge, if deleted, disconnects the most? |
| `algo_nodes.csv` → `dom_cut`, `idom`, `algo_critical_edges.csv` | Dominator tree from the axioms ("any path suffices" reading) | Which theorems lose *every* path from the axioms if X is deleted? |
| `percolation.csv`, `glue_components.csv` | Sequential node deletion with union-find (Newman–Ziff), three orders | How many deletions until the library falls apart, and does the order matter? |
| `algo_nodes.csv` → `community`, `part_in`, `part_out`; `communities.csv` | Louvain, citations weighted by 1/(times the lemma is cited); participation coefficients | Which areas does the library split into? Which proofs draw on several areas? |
| `algo_nodes.csv` → `pagerank` | PageRank, importance flowing from a theorem to the lemmas it cites | Recursive "cited by important theorems" |
| `algo_nodes.csv` → `log10_paths`, `path_frac` | Exact path counting on the DAG (big integers) | How many axiom→leaf dependency chains run through X? |

### Findings so far

- **Single deletions never matter.** The biggest split from deleting one edge is 2 theorems; from one node, 3. The dominator tree is flat as well: 99.4% of theorems are dominated only by the root, and no theorem dominates more than 5 others. So the literal "which edge splits the graph most" question has a boring answer: the library is massively redundant. This is the single-proof degeneracy from section 3 showing up in the data.
- **It takes mass deletion to break it, and order matters.** Deleting statements most-cited first breaks the largest component below half of what's left after **14,000** deletions (44%). Most-reach first takes 21,000; random order takes 30,500. Even after removing the 300 most-cited lemmas, 99.9% of what remains is one component.
- **Unweighted communities group theorems by proof style, not topic.** Plain Louvain makes clusters around `syl`/`adantr` (deduction-style proofs) vs `ax-mp`/`mp2an` (closed-form proofs), with NMI 0.28 against the human chapters. Weighting each citation by 1/(times the lemma is cited) gives 64 topical communities (Topology, Integrals, Hilbert-space operators, Categories, Tarskian geometry, …) and NMI 0.49. Dropping the top 300 hubs only reaches 0.37.
- **"Draws on many communities" (`part_in`) finds synthesis proofs**, such as lemmas for Sylow's theorems (`pgpssslw`), uncountability of the reals (`ruclem1`) and the Alexander subbase theorem (`cmpsublem`). The opposite direction (`part_out`) is topped by glue lemmas, as expected.
- **Dependency-chain counts pick out a highway**: about 10^36.5 axiom→leaf chains pass through the complex-exponential theorems (`eff1o`, `efif1olem4`, `pilem3`), where foundations funnel into analysis.

### Caveats

- Participation is noisy for theorems with only a few lemmas (2 lemmas in 2 communities already scores 0.5).
- Louvain is randomised (`--seed`); community ids change between seeds, and the counts shift slightly.
- Path counts are dominated by long chains, so they reward sitting deep in the middle of the library, not being important in a human sense.

---

## 13. Track B: the generated universe

### Running it

```bash
# 1. Human reference list: 196 Principia theorems with shortest known proofs (replays and checks every proof)
curl -L -o data/raw/pmproofs.txt https://us.metamath.org/mmsolitaire/pmproofs.txt
python3 -m logicgraph.pmproofs data/raw/pmproofs.txt data/pm/pm_theorems.csv

# 2. Generate every theorem provable in <= 21 steps  (~40 s; 228,480 theorems, 754,549 derivations)
python3 -m logicgraph.generate data/gen/luk21 --max-steps 21
python3 -m logicgraph.generate data/gen/luk19 --max-steps 19     # second horizon, for the stability check

# 3. Scores on the AND-OR hypergraph  (~25 s)
python3 -m logicgraph.hyperscores data/gen/luk21
python3 -m logicgraph.hyperscores data/gen/luk19

# 3b. Supernodes: collapse near-duplicates, score each supernode  (~20 s)
python3 -m logicgraph.supernodes data/gen/luk21
python3 -m logicgraph.supernodes data/gen/luk19

# 4. Validation report -> data/gen/luk21/validation.md
python3 -m logicgraph.validate data/gen/luk21 --compare data/gen/luk19

# 5. Visualizer: open http://localhost:8765/explorer.html?data=gen
python3 -m logicgraph.gen_export data/gen/luk21 viz/data_gen.js

# Tests
python3 -m unittest discover tests
```

Other axiom sets: `--axioms implicational` (ax-1, ax-2) or a comma-separated list in Polish notation, e.g. `--axioms CpCqp,CCpCqrCCpqCpr,CCCpqpp`.

### How it works

| Module | What it does |
|---|---|
| `formula.py` | Formulas as nested tuples, unification, condensed detachment, canonical form, truth-table check, three notations (Polish, pmproofs infix, set.mm ASCII), D-proof replay. |
| `pmproofs.py` | Reads Metamath's `pmproofs.txt` and verifies every proof in it with our engine. |
| `generate.py` | Enumerates by proof length: a theorem with an n-step shortest proof is `D a b` for theorems with i- and j-step shortest proofs, i + j = n − 1. Trying every such pair finds everything, with no dependence on search order. Records **every** derivation. |
| `subsumption.py` | Marks redundant theorems: instances of another theorem that is no longer to prove (`p → (p → p)` is just ax-1). |
| `hyperscores.py` | Re-solves shortest proof lengths with one theorem (or a whole set) made free ("named") or forbidden ("banned"). |
| `supernodes.py` | Collapses near-duplicate theorems into supernodes at three levels and scores each supernode. |
| `validate.py` | AUC against human names, matched-control AUC, horizon stability, top unnamed theorems. |
| `gen_export.py` | Writes the scored library in the set.mm pipeline's schema so the same visualizer shows it. |

**The graph is an AND-OR hypergraph.** A node is a theorem; a hyperedge is one derivation `(major, minor) → conclusion`. Proof length `L(t)` is the D-proof length (tree size), the measure `pmproofs.txt` uses.

**Horizon rule.** Generating to N steps records exactly the derivations with `L(major) + L(minor) + 1 ≤ N`. So a re-solved length is exact whenever it is ≤ N, and "above N" is always truly above N. Naming gain is a lower bound, because a proof that gets shorter by using the named lemma several times can have a full expansion longer than N.

**Library and candidates.** Scores sum over the *library*: non-redundant theorems with `L ≤ N − 4`. *Candidates* for gain and knockout are non-redundant theorems with `L ≤ N − 6`. Redundant theorems stay in the graph as possible proof steps.

### Results at N = 21

- 21,241 theorems are provable in ≤ 17 steps; **62% are redundant instances**, leaving a library of 8,111 and 2,890 candidates.
- 14 library theorems carry a human name (Principia number or set.mm label); 12 are candidates. **None of the named theorems is redundant.**

| Score | AUC (95% interval) | AUC vs controls of the same size and proof length |
|---|---|---|
| **Naming gain** | 0.92 (0.86–0.97) | **0.90 (0.78–0.99)** |
| Knockout | 0.82 (0.69–0.95) | 0.52 (0.36–0.69) |
| Lost if removed | 0.58 (0.49–0.70) | 0.59 (0.47–0.74) |
| Deep (steps ÷ size) | 0.90 (0.81–0.97) | n/a (a function of size and length) |
| Baseline: small statement | 0.99 (0.99–1.00) | n/a |
| Baseline: short proof | 0.84 (0.69–0.97) | n/a |
| Baseline: times used as a premise | 0.86 (0.73–0.97) | 0.64 (0.49–0.78) |

AUC is the chance that a named theorem outranks an unnamed one; 0.5 is chance. Full report: `data/gen/luk21/validation.md`.

### Findings

- **Naming gain carries real signal.** It still separates named from unnamed theorems when each named theorem is compared only with unnamed ones of the same size and proof length. Its top-ranked candidate of 2,890 is `(p → q) → ((r → p) → (r → q))`: Principia's *Syll* (*2.05), set.mm's `imim2`.
- **Knockout does not.** Its raw AUC of 0.82 falls to 0.52 under the matched control: it was measuring proof length. The same goes for "affected if removed".
- **Statement size alone scores 0.99.** In this range humans named the short statements. Any score has to be judged by the matched column, not the raw one.
- **Deep works on its own terms.** The top theorem by steps ÷ size among 8,111 is `¬¬p → p` (double-negation elimination); third is `p → (¬p → q)` (pm2.24); eleventh is `p → ((p → q) → q)` (pm2.27).
- **Rankings are stable across horizons.** Between N = 19 and N = 21, naming gain has Spearman 0.987 and an identical top 20; knockout 0.948.
- **What each axiom buys** (library theorems with no proof left inside the horizon): without ax-1, 99.7%; without ax-2, 99.8%; without ax-3, 64.8%.
- **Unnamed high scorers** (candidate findings), by naming gain: `(p → (q → r)) → (s → ((p → q) → (p → r)))`, `p → ((q → (p → r)) → (q → r))`, `(p → (q → (r → s))) → ((p → q) → ((p → r) → (p → s)))`. By deep: `¬(p → p) → q`, `((p → p) → q) → q`, `(p → ¬p) → (p → q)`.

### Caveats

- **Thin ground truth.** 12–14 named theorems. Many Principia numbers expand to the same formula (196 entries, 157 distinct), and only 17 distinct formulas have proofs of ≤ 21 steps. The intervals are wide and the matched comparison uses 9 of them.
- **Short proofs only.** More than half of the published Principia proofs (115 of 196) are longer than 51 steps; our horizon is 21. The C++ tool `pmGenerator` has reached 39 steps at a cost of hundreds of GB.
- **Naming gain is a lower bound** (see the horizon rule), and it is measured against one library definition (all non-redundant theorems up to N − 4, equally weighted).
- **Tree size is one cost measure.** A proof that reuses a lemma pays for it every time. That is exactly what makes naming valuable here, so a DAG-size measure could give a different picture.
- **One axiom system.** Proof lengths, and so every score, are relative to ax-1, ax-2, ax-3.

### Supernodes: collapsing near-duplicates

Every generated theorem is a tautology, so "logically equivalent" would merge everything. Supernodes use syntactic relations instead, and each level merges whole supernodes of the level below:

| Level | Merges | Supernodes (of 21,241 theorems with ≤ 17-step proofs) | Example |
|---|---|---|---|
| 1 · redundancy | special cases into the more general theorem | 8,114 | `p → (p → p)` joins ax-1 |
| 2 · + weakening | `q → A` (q a fresh "dummy hypothesis") into A | 5,221 | set.mm's `ax1w` joins ax-1; `idd` joins `p → p` |
| 3 · + exchange | hypotheses in any order; fresh hypotheses anywhere dropped | 4,694 | Principia's *2.05 and *2.06 (both called "Syll") merge; so do *2.21 and *2.24 |

Two other definitions were tried and rejected. "Derivable from each other in one step using a short helper lemma" puts almost everything in one supernode (7,650 of 8,114 with helpers of ≤ 3 steps), because any theorem A gives `q → A` in one step and back. Level 3 is already aggressive: it merges ax-1 `p → (q → p)` with `p → p`, and modus ponens `p → ((p → q) → q)` with `(p → q) → (p → q)`.

Supernode scores free or forbid **every member at once**, and the library becomes the set of supernodes (a supernode's proof length is its shortest member's). In the explorer (`explorer.html?data=gen`), the *Collapse* menu redraws the graph with supernodes, the details panel lists a theorem's supernode at each level with its members, and the leaderboard can rank supernodes.

**Validation at each level** (matched AUC = against unnamed supernodes of the same representative size and proof length; full tables in `validation.md`):

| Level | Named supernodes | Naming gain, matched AUC | Knockout, matched AUC |
|---|---|---|---|
| 1 | 12 | 0.89 (0.75–0.99) | 0.51 (0.35–0.68) |
| 2 | 10 | 0.84 (0.63–0.98) | 0.40 (0.23–0.59) |
| 3 | 6 | 0.70 (0.44–0.93) | 0.29 (0.10–0.50) |

- **Collapsing cleans up the graph but does not improve the validation.** The hope was that knockout fails because near-variants stand in for each other when one is banned. Banning whole supernodes rules that out, and knockout gets no better. Whatever makes named theorems special, "the library can't do without them" is not it here.
- **Naming gain stays the best score**, and the merged "Syll" supernode (*2.05, *2.06, `imim1`, `imim2`; 68 members) ranks 1st of 1,650 non-axiom supernodes at level 3. Its decline at higher levels rests on very few named supernodes (6 at level 3), so it may be noise.
- **Rankings stay stable across horizons**: naming gain Spearman 0.987 / 0.972 / 0.963 at levels 1 / 2 / 3.
- **Level 2 is the sensible default view.** It removes padded copies without merging things humans keep apart.

### Next

- More ground truth: named theorems from other sources, or a larger horizon by importing `pmGenerator`'s published proof files.
- Axiom ablation with certificates: ax-1 + ax-2 only, then adding Peirce's law, with 3-valued countermodels to prove "needs the axiom".
- The same scores under other axiom systems, to see which theorems stay important.

---

## 14. Assumptions: the map of logics

The question behind the project: which principles have to be taken at face value, and what happens if one of them is false? "The axioms" are a presentation choice (Meredith's single axiom proves the same classical logic as Łukasiewicz's three), so the map is drawn between **logics**, and what separates them is **independence**: principle P does not follow from base B.

### Running it

```bash
# ~25 min the first time (proof searches are cached in data/logics/cache/), ~1.5 min after
python3 -m logicgraph.logicmap data/logics --library data/gen/luk21
python3 -m logicgraph.gen_export data/gen/luk21 viz/data_gen.js     # adds each theorem's weakest logic
# visualizer: http://localhost:8765 (the logic map, section 17)
```

| Module | What it does |
|---|---|
| `intuitionistic.py` | Exact decision procedure for minimal and intuitionistic logic (Dyckhoff's terminating sequent calculus G4ip, with ¬A read as A → ⊥). No horizon. |
| `matrices.py` | Countermodels: finite Heyting algebras (down-sets of posets with up to 4 points, every choice of what ⊥ means) and every 2- and 3-valued truth table. |
| `principles.py` | Minimal logic (ax-1, ax-2, reductio) and 13 named principles in implication and negation. |
| `logicmap.py` | For each base logic and principle, a certificate either way; groups bases into logics; tags the generated library. |

### How a question gets settled

For a base logic B and a principle P, in this order:

| Status | Certificate | Certain? |
|---|---|---|
| refuted | A truth table (2–16 values) where all of B holds, modus ponens preserves truth, and P fails. | Yes: B never proves P, at any length. |
| proved | An explicit condensed-detachment proof from B's axioms (search to 17 steps, then 19 for open cases). | Yes. |
| chained | B proves all axioms of another base B′, and B′ proves P. | Yes. |
| instance | Minimal / intuitionistic / classical logic (whichever B contains) proves "instance of B's principle → P", checked by the decision procedure. | Yes, given completeness of those Hilbert systems (standard). |
| decided | P is a theorem of a logic B contains (decision procedure; truth tables once B proves ax-3). | Same. |

Bases: minimal, minimal + each of the 9 non-minimal principles, intuitionistic + each of the 7 non-intuitionistic ones (17 bases × 13 principles = 221 cells). **All 221 are settled; none is unknown.**

### The map

```
                       classical
               (= minimal + DNE, ax-3, classical reductio or Mendelson's axiom;
                = intuitionistic + any classical principle, Peirce's law included)
                 /                                   \
     minimal + Peirce                           intuitionistic (+ explosion)
        /         \                                 /
 minimal + CM    minimal + ¬¬(¬¬p → p)  ───────────┘
 (= minimal + proof by cases)     \
        \                          \
                    minimal
```

Six logics, seven edges, every edge certified strict by a countermodel.

- **Double-negation elimination, ax-3, classical reductio and Mendelson's axiom each give full classical logic on their own**, even over minimal logic.
- **Peirce's law, consequentia mirabilis and proof by cases do not.** Over minimal logic they give three strictly weaker logics, each refuted for explosion by the 2-valued world where "⊥" is true. Add explosion (intuitionistic logic) and every one of them becomes classical. Peirce's law reaches classical through its instance `((p → ¬p) → p) → p`.
- **Peirce's law is strictly stronger than consequentia mirabilis over minimal logic**: Peirce's law proves `¬¬(¬¬p → p)`, and consequentia mirabilis does not.
- **`¬¬(¬¬p → p)` sits below both Peirce's law and intuitionistic logic.** It is intuitionistically valid but not minimally valid, so minimal logic does not satisfy Glivenko's theorem.

### The generated library through this lens

Of the 8,114 non-redundant theorems with proofs of ≤ 17 steps from ax-1, ax-2, ax-3 (decided exactly, theorem by theorem):

| Weakest logic that proves it | Theorems |
|---|---|
| minimal | 2,885 (35.6%) |
| intuitionistic, not minimal | 161 (2.0%) |
| classical only | 5,068 (62.5%) |

Each node's share of the library: minimal 2,885; minimal + Peirce 2,885–2,892; minimal + CM 2,885–2,891; minimal + ¬¬(¬¬p → p) 2,885–2,889; intuitionistic 3,046; classical 8,114. (Ranges are lower bounds from the decision procedures and upper bounds from countermodels.) **Peirce's law alone buys at most 7 of the 5,229 theorems beyond minimal logic; explosion alone buys 161; together they buy all of them.**

### If a principle were false

The least a principle's falsity costs: among small worlds (truth tables with ≤ 4 values) where minimal logic holds and the principle fails, the one that breaks the fewest library theorems.

| Principle false | Library theorems that fail too, at least | Gentlest world found |
|---|---|---|
| any classical principle (DNE, Peirce, CM, ax-3, …) | 5,068 (62%) | Gödel's 3-valued logic: everything intuitionistic survives |
| explosion | 5,222 (64%) | 2-valued, ⊥ read as true: Peirce, CM, proof by cases survive |
| ¬¬(¬¬p → p) | 5,223 (64%) | 3-valued Heyting, ⊥ = middle value |

Every classical principle has the same gentlest world, and it costs exactly the classical-only theorems. Losing explosion costs more, even though explosion is the weaker assumption. The weakest-looking principle, `¬¬(¬¬p → p)`, is the most expensive to lose. These are upper bounds on the true minimum: only 41 small models (6 distinct patterns over the catalog) are searched.

### Caveats

- **Language: implication and negation only.** "Or" is defined classically there, so excluded middle (`p ∨ ¬p`) and De Morgan laws can't be stated faithfully yet; proof by cases and consequentia mirabilis stand in for them. Adding "and"/"or" as primitives is the next extension.
- **Only single-principle extensions are mapped** (plus intuitionistic + one). Combinations such as minimal + Peirce + ¬¬(¬¬p → p) are not separate bases yet; with these results they collapse onto existing nodes or classical.
- **"Instance" and "decided" rely on the completeness of the standard Hilbert systems** for minimal, intuitionistic and classical logic in this language. "Refuted" and "proved" rely on nothing.
- **Breakage uses small models only**; a gentler world with more values could exist.
- **Related work:** Diener and McKubre-Jordens (2020) classify classical principles over minimal logic by hand; this map reproduces that kind of picture by machine, with certificates.

---

## 15. Modal logic: the cube, and the bridge from intuitionistic logic

Same question, with □ ("necessarily"; ◇ "possibly" = ¬□¬). Every logic is **K** (classical logic, `□(p → q) → (□p → □q)`, and "if A is a theorem, so is □A") plus some of:

| Principle | Formula | Frame property it matches |
|---|---|---|
| D | □p → ◇p | every world sees some world |
| T | □p → p | every world sees itself |
| B | p → □◇p | seeing is symmetric |
| 4 | □p → □□p | seeing is transitive |
| 5 | ◇p → □◇p | euclidean |
| .2 | ◇□p → □◇p | confluence |
| Löb | □(□p → p) → □p | □ read as "provable" (Gödel–Löb provability logic) |

### Running it

```bash
python3 -m logicgraph.modalmap data/logics --library data/gen/luk21     # map in seconds; the bridge check takes a few minutes
# visualizer: the "Logics" tab, below the first map
```

| Module | What it does |
|---|---|
| `modal.py` | Modal formulas; all Kripke frames with up to 4 worlds (66,066) and vectorized frame validity; exact tableau provers for K and S4 (S4 with loop checking); an S5 check by clusters; the Gödel–McKinsey–Tarski translation. |
| `modalmap.py` | Certificates for 35 bases × 7 principles, the logics and edges, and the bridge check. Reuses the chaining and node grouping from `logicmap.py`. |

### How a question gets settled

| Status | Certificate |
|---|---|
| refuted | A Kripke frame (≤ 4 worlds) where every axiom of the base is valid and the principle is not. Frame validity survives modus ponens, necessitation and substitution, so this is certain. |
| instance | The K prover shows "these instances of the base's axioms, each also under □ and □□, imply the principle"; necessitation and modus ponens finish the proof. |
| decided | The principle is a theorem of K, or of S4/S5 when the base contains them (exact provers). |
| chained | As before: the base proves another base's axioms, and that base proves the principle. |

The provers are tested against Kripke semantics (every K or S4 theorem must hold on every small frame of the right kind; anything refuted on a small frame must be reported a non-theorem), and against each other through the translation (below).

### Results

All 245 cells are settled; none is unknown. Building the map takes about 2 seconds.

- **The 32 combinations of D, T, B, 4, 5 collapse into exactly 15 logics**, the textbook "modal cube", with every one of its 26 cube edges certified strict by a frame. Highlights: S5 has 13 presentations here (KT5 = KTB4 = KDB4 = KDB5 = …); KB4 = KB5 = KB45; KT = KDT.
- **The certificates are real proofs.** T gives D through the instance `□◇p → ◇p` (with □ applied to it); B and 4 give 5; D, B and 4 together give T. **Löb's axiom gives 4** through the instance with `p ∧ □p`, which is the textbook proof, found by search.
- **.2 and Löb sit off the cube:** K.2 lies below both KB and K5 (each of B and 5 proves .2); S4.2 lies strictly between S4 and S5 (a 3-world "fork" refutes .2 in S4); GL lies above K4 and is incomparable with the reflexive logics.

### The bridge

The Gödel–McKinsey–Tarski translation (p ↦ □p, ¬A ↦ □¬A*, A → B ↦ □(A* → B*)) reads intuitionistic logic inside modal logic. A formula is an intuitionistic theorem exactly when its translation is an S4 theorem, and a classical theorem exactly when its translation is an S5 theorem. So **the S4 → S5 edge of the modal map is the intuitionistic → classical edge of the first map**, seen from inside modal logic.

Checked on the generated library, on a sample of 761 theorems: all 161 that need explosion (intuitionistic, not minimal), and 300 each from the minimal and classical-only tags. The two decision procedures are independent programs (G4ip for intuitionistic logic, the S4 tableau), so agreement is a strong check on both.

| Check | Result |
|---|---|
| Intuitionistic tag agrees with S4 validity of the translation | **654 of 654** decided, **0 disagreements** |
| S4 check over the 10 s limit (counted, not guessed) | 107 |
| Translation is an S5 theorem (every library theorem is classical) | **425 of 425** with ≤ 4 letters (336 with more letters not checked) |

| Principle | Translation | S4 | S5 |
|---|---|---|---|
| double-negation elimination `¬¬p → p` | `□(□◇□p → □p)` | ✗ | ✓ |
| Peirce's law | `□(□(□(□p → □q) → □p) → □p)` | ✗ | ✓ |
| explosion `¬p → (p → q)` | `□(□¬□p → □(□p → □q))` | ✓ | ✓ |

### Caveats

- **Countermodels have at most 4 worlds.** Enough for everything here; principles needing larger or infinite frames would show up as unknown.
- **"Instance" certificates rely on the K tableau**, which is checked against frame semantics and the intuitionistic prover but is not a formally verified program.
- **S4 is hard (PSPACE-complete) and the S4 prover is a straightforward tableau**, so some translated library theorems exceed the time limit; they are counted and reported, not guessed.
- **The S5 check enumerates clusters**, so it covers theorems with at most 4 letters.

---

## 16. Sandbox: add and remove assumptions

*Superseded by the logic map page (section 17), which uses the same engine; the sandbox described here is still in `explorer.html?data=gen` under the Logics tab.* The Logics tab starts with a sandbox. Switch any principle off or on, or type a new assumption, and both maps are recomputed **in the browser** in about a second: which logics exist, how they are ordered, and a certificate for every step. A "What changed" panel lists logics that appeared, disappeared, merged or split, and edges gained or lost. New logics get a dashed outline. For an added assumption it also reports:

- where it lands on its own: an existing logic (with what it is equivalent to) or a new one (with its neighbours)
- what it proves and what it follows from
- what it is independent of, in both directions
- for the propositional map, how many generated library theorems the new logic proves

Input: `->`/`→`, `~`/`¬`/`!`, `[]`/`□`, `<>`/`◇`, `&`, `|`, `<->`, any lowercase letters as variables; or Łukasiewicz Polish notation (C, N, K, A, E, L, M). A formula with □ or ◇ goes on the modal map, anything else on the propositional one. The live preview says which map and what the formula already is (a theorem of minimal logic, intuitionistic logic, classical logic, K, S4, or none of these). Added assumptions are remembered in the browser.

### How it works

`viz/sandbox.js` is a port of the Python engine, without the brute-force proof generator:

| Piece | Python original |
|---|---|
| Countermodels: Heyting algebras from posets (≤ 4 points), all 2- and 3-valued matrices, all Kripke frames with ≤ 4 worlds | `matrices.py`, `modal.py` |
| Exact deciders: G4ip (minimal/intuitionistic), truth tables, K and S4 tableaux, S5 by clusters | `intuitionistic.py`, `modal.py` |
| Instance search, chaining, grouping into logics, covering edges | `logicmap.py`, `modalmap.py` |
| Library bounds and "if false, at least" (from small-model data exported by `logicmap.py`) | `logicmap.py` |

Without the proof generator, "follows" certificates come from the decision procedures, instances and chaining. They settle every cell of both default maps.

The bases are every combination of up to N principles (default 3, adjustable). That is more than the Python maps check, so the sandbox's default maps are richer:

- **Propositional: 7 logics instead of 6.** Combining consequentia mirabilis with `¬¬(¬¬p → p)` gives a logic strictly between each of them and Peirce's law. Gödel's 3-valued logic with ⊥ read as the top value refutes Peirce's law there.
- **Modal: 24 logics instead of 18.** Löb's axiom with D or T is **inconsistent** (no frame validates both), and Löb with B or 5 is **Ver**: every world is a dead end, □⊥. The sandbox detects and labels both cases.

Examples of what it finds:

| Change | What the sandbox reports |
|---|---|
| Add `((p -> q) -> q) -> ((q -> p) -> p)` | Over minimal logic it is equivalent to Peirce's law; independent of explosion; the map's shape doesn't change. |
| Add McKinsey's axiom `[]<>p -> <>[]p` | It proves D and is independent of T, B, 4, 5, .2 and Löb. 11 new logics appear. S5 + McKinsey sits strictly between S5 and "inconsistent", because in S5 it says possibility implies necessity. |
| Switch explosion off | Intuitionistic logic and its two edges disappear. |
| Add a non-tautology such as `p -> q` | The logic is flagged inconsistent: it proves everything. |

### Checks

`tests/test_sandbox.py` runs the JavaScript engine under Node:

- **Parity:** on the Python maps' own principles and bases, it must give the same logics, the same edges, and the same verdict for every cell (221 propositional, 245 modal). It does, with no unknowns.
- **Library numbers:** library bounds and breakage must match Python's exactly.
- **Scenarios:** the parser, a re-written Clavius law joining consequentia mirabilis, removing explosion, the degenerate modal logics, and a non-tautology.

### Limits

- **Proofs are certificates, not proof texts.** The sandbox shows *why* something follows (an instance and a decision procedure, or a chain), not a step-by-step derivation.
- **Small models only.** Countermodels have at most 4 values or 4 worlds. For modal formulas with 3 or more letters, only frames with up to 3 worlds are checked, to keep it fast. Anything unsettled is shown as unresolved, not guessed.
- **The instance search has a time budget** (0.4 s per question), so a hard question can stay unresolved. McKinsey's axiom leaves 2 such cells.
- **∧, ∨ and ↔ were abbreviations defined classically** here. The propositional map in section 18 replaces this: ∧, ∨ and ⊥ are now real connectives.

---

## 17. The logic map page

`viz/index.html` (http://localhost:8765 with the server from section 11) is now a single page built around the graph. The older theorem explorer and overview moved to `viz/explorer.html`.

- **The graph fills the page**, styled after The Pudding: a deep aubergine background, dots and thin lines, serif and grotesque type, and mono "pills". The logic you are in is a large white dot with a halo. The lines up from it (one assumption away) are white and labelled with what they add. Dots and labels keep their size as you zoom (scroll) or pan (drag).
- **Top right:** switch between **Propositional** and **Modal**, and pick any logic by name.
- **Bottom:** a one-line caption says where you are (or what your last change did), and your assumptions sit underneath as pills. Click a pill to **drop** it. **+ Add an assumption** opens a short list ("5 → S5", "D · already true") plus a box to type your own formula.
- **Click a line** to see why it is a real step up (the countermodel, drawn as a small world diagram or truth table). **Click a logic** to move there.

### Baked-in assumptions

Some assumptions follow from others. In S5 written as T + 4 + 5, 4 is redundant because T + 5 already proves it. Baked-in assumptions show as dashed lavender pills (hover for what they follow from), and the caption says when a change bakes something in or when dropping one changes nothing. This is computed for every subset of your assumptions, using the same certificates as the maps (countermodels, decision procedures, instances, chaining).

What this looks like in practice:

| From | Action | What the page says |
|---|---|---|
| S4 (T + 4) | add 5 | Moves to S5. **4 is now baked in**: it follows from T + 5. B and .2 become true. |
| S5 (T + 4 + 5) | break 4 | **Changes nothing**: 4 was baked in. Still S5. |
| S5 (T + 5) | break 5 | Down to KT; B, 4 and .2 are no longer true. |
| KD (D) | add T | D becomes baked in: it follows from T. |
| K4 (4) | add Löb | 4 becomes baked in: Löb's axiom proves it. You are in GL. |
| KB (B) | add 4 and 5 | Each of 4 and 5 is baked in by the other with B: break either one, not both. |
| intuitionistic (weakening + contraction + explosion) | add Peirce's law | Moves to classical. **Weakening and contraction are now baked in**: Peirce's law proves both (section 18). |
| classical | add double-negation elimination | DNE was already true (from explosion + Peirce). |

The add list previews where each assumption takes you before you click: for example, from S4 it shows "5 → S5" and "D · already true".

### Checks

`tests/test_sandbox.py` includes the baked-in cases above: T + 5 bakes in 4, D comes from T, Löb gives 4, the B + 4 + 5 mutual case, T + B + 4 with nothing redundant, and on the propositional side explosion + Peirce ⇔ DNE, and Peirce's law baking in weakening and contraction.

---

## 18. The breakable floor: ∧, ∨, ⊥ and the structural rules

The propositional map used to start at minimal logic, in a language with only → and ¬. It now starts lower and says more:

- **∧, ∨ and ⊥ are real connectives**, and ¬p means p → ⊥. Excluded middle (`p ∨ ¬p`), weak excluded middle (`¬p ∨ ¬¬p`), linearity (`(p → q) ∨ (q → p)`), non-contradiction and distribution can now be stated.
- **The floor is breakable.** Every logic on the map keeps a small core: hypotheses can be used in any order (exchange), implications chain, p → p, and ∧ / ∨ mean "both" / "either". That core is the →∧∨ part of intuitionistic linear logic. Two structural rules sit on top as ordinary assumptions you can drop:

| Rule | Formula | What it says |
|---|---|---|
| weakening | p → (q → p) | an unused hypothesis does no harm |
| contraction | (p → (p → q)) → (p → q) | a hypothesis may be used twice |

Core alone is **linear** logic; core + weakening is **affine**; core + contraction is **relevant** (without distribution, so Meyer's LR rather than R); core + both is **minimal** logic. Explosion on top gives intuitionistic logic, and so on up to classical. On the page, the two rules are the first two pills (grey, set apart), and the graph puts affine logics on the left wing and relevant ones on the right.

### How cells are settled

| | Method | Exact? |
|---|---|---|
| linear, affine | sequent search (contexts are multisets; no contraction, so every rule shrinks the sequent) | yes |
| relevant | the same with contraction, at most 2 copies per branch | sound, bounded |
| minimal, intuitionistic | G4ip with ∧ and ∨ (⊥ is an ordinary atom in minimal logic) | yes |
| Gödel–Dummett | the (k+2)-element Gödel chain | yes |
| classical | truth tables | yes |
| everything else | instances of the base's principles, then one of the above | sound |

The instance step changed in one important way. A proved principle is a theorem, so it can be used any number of times, or not at all. Linear logic treats such formulas as `!A`. The search now puts instances in an unrestricted zone of the sequent instead of using each exactly once. Without this it couldn't find proofs by cases, where a principle is needed in only one branch.

**Countermodels** are finite algebras: Heyting algebras of posets with up to 4 points, with every choice of ⊥; every implication table on 2- and 3-element chains that models the core; every commutative residuated lattice on lattices with up to 5 elements (including the non-distributive N5 and M3), with every ⊥. That is 1,385 models, built in about 0.25 s.

Two separations need bigger algebras: affine logic not proving distribution, and affine logic with double negation not proving linearity. No algebra with weakening on 5 or fewer elements breaks either. An offline search of every residuated lattice with weakening on 6- and 7-element lattices (981 of them, 1.5 s) found four that settle every case. They are embedded as tables in `sandbox.js` (`SEARCHED`).

### What the map shows

With every combination of the two rules, one principle at a time below minimal logic and up to three above it, the default map has **33 logics and 61 edges, with every cell settled and every edge certified** (0.8 s in the browser). Some findings, each with a certificate:

| Finding | Why |
|---|---|
| **Peirce's law bakes in weakening and contraction.** Linear + Peirce = minimal + Peirce. | Peirce with q := q → p proves weakening using each hypothesis exactly once. |
| **Łukasiewicz's axiom** `((p → q) → q) → ((q → p) → p)` also bakes in weakening. | Same trick, found by the engine when the axiom was typed in. |
| Excluded middle + explosion prove contraction, even in linear logic. Excluded middle alone does not. | Proof by cases: one branch has the extra copy of p; the other has ⊥. |
| With weakening, double negation proves explosion. Without weakening it doesn't. | From ⊥, weakening gives ¬¬p. |
| Non-contradiction `¬(p ∧ ¬p)` needs contraction. | ∧ hands over only one conjunct; using both needs two copies. |
| Distribution needs both rules. | It fails in a 6-element affine algebra (found by the search) and in a relevant algebra on the 5-element pentagon N5. |
| Above intuitionistic logic: Jankov's logic (weak excluded middle) and Gödel–Dummett (linearity). | As expected. |

### Checks

`tests/test_sandbox.py` (Node):

- **Parity:** run with weakening and contraction in every base, the engine reproduces the old Python propositional map exactly (6 logics, same edges, 221 cells), and the modal map as before.
- **Provers against models:** on 600 random formulas, anything a prover proves holds in every model of that logic, and linear ⊆ affine, relevant ⊆ minimal ⊆ intuitionistic ⊆ Gödel–Dummett ⊆ classical. A wider run of 1,500 formulas found no contradiction either.
- **Known facts** for each decider, and the findings above: Peirce's collapse, excluded middle + explosion → contraction, the searched model refuting distribution, no unknowns, no uncertified edges.

### Limits

- **The relevant-logic search is bounded.** Relevant logic with ∧ and ∨ is decidable but very hard. A "no" there is a countermodel; a missing "yes" can stay unknown.
- **Library numbers are gone from the page.** The generated library (section 13) is in the →¬ language with ax-1..3, so it doesn't apply below minimal logic. The Python map (`logicmap.py`) still computes them for the old map.
- **The Python side is unchanged.** `logic_map.json` is still the →¬ map over minimal logic. The page no longer loads it; the new map exists only in `sandbox.js`.

## 19. Discovery: searching for formulas that do something unexpected

The map answers "what does this set of named principles give you?". The search turns that around: take **every** small formula, add it on its own to a starting logic, and see what it brings in.

```
node scripts/discover.js            # all five starting logics in parallel; --vars 2 --ops 5 by default
```

For each classically true formula φ in p and q with up to 5 connectives (→ ∧ ∨ ¬) that the starting logic F doesn't already prove, the engine asks two questions:

1. **Which named principles does F + φ prove?** Call that set P.
2. **Does F + P prove φ back?**
   - **Yes:** φ is a single formula that does the work of all of P. If P contains a structural rule (or explosion) that φ doesn't state, φ smuggles it in. Peirce's law was the first example; the search finds the rest.
   - **No:** F + φ is a logic that isn't on the map. It proves exactly the principles P from the list, yet it is strictly stronger than F + P. A finite countermodel (F + P holds, φ fails) certifies the gap.

Formulas that hold in exactly the same finite models are tested once (the shortest), and formulas that are literally a named principle are skipped. Answers carry the same certificates as the map; anything the engine can't settle within its time budget is counted as "unsettled" and not reported.

Results go to `data/discoveries.json` (and `viz/discoveries.js` for the page). On the page, **Discoveries** opens a panel for the starting logic you're in; **Try it** adds the formula there so the map shows what it does.

### What it found (2 letters, ≤ 5 connectives)

The full run took about 2.3 hours on a laptop (five processes in parallel; linear logic is the slowest). From 9,500–32,700 candidate formulas per starting logic, 440–1,155 distinct ones were tested; 2–256 per logic couldn't be settled in the time budget (most in relevant logic, whose search is bounded).

| Starting logic | Formula | Result |
|---|---|---|
| linear | `(p ∧ (p → q)) → q` (modus ponens as one formula) | Exactly contraction + non-contradiction. |
| linear | `p → ((q ∨ ¬p) → q)` (disjunctive syllogism) | Exactly weakening + explosion. |
| linear | `¬(p → q) → p` | Exactly weakening + explosion + double negation. |
| linear | `(p → q) ∨ (q → (p ∧ (p → q)))` | Exactly weakening + linearity + distribution. |
| linear | `p ∨ (p → q)` | Contraction, excluded middle and more, yet strictly stronger than those together. |
| linear | `p → (p → p)` (the mingle axiom of relevance logic) | None of the named principles, but a new logic (840 formulas behave like this). |
| affine | `(¬p → (q ∧ ¬q)) → p` | Everything up to classical logic, contraction included. |
| relevant | `((p → (p → q)) → p) → p` (Peirce's law with p used twice) | Weakening and the whole classical package except explosion. |
| intuitionistic | `p → (q ∨ ¬q)` and 322 others | Classical logic. |
| intuitionistic | `p ∨ ((p → q) ∨ ¬q)` | Above Gödel–Dummett, below classical. This matches the known 3-valued Gödel logic: the search found it without being told. |

`node scripts/discover.js --regroup` regroups saved results without searching again (used once to stop counting principles the starting logic already proves as "gained").

Tests: `tests/test_discover.py`.

**Caveats.** The search certifies facts; it doesn't know which are new to the literature. Several above are known results (mingle, disjunctive syllogism and explosion, the Gödel logics). Formulas are grouped by which finite models they hold in, so two formulas that agree on every model are treated as one (the shorter is tested). "Try it" on the page recomputes the whole map in the browser, which can take several seconds. "Logics that aren't on the map" are many: the space between linear and classical logic is huge, so the page shows the shortest few per profile.

## 20. The lemma contest, and whether tree size does the work

Two follow-ups to the naming-gain result in section 13, which rested on only 12 named theorems.

```
python -m logicgraph.lemma_contest data/gen/luk21     # ~12 min; writes lemma_contest.{md,json} there
```

Full report: [lemma_contest.md](lemma_contest.md).

### 1. The contest

Instead of asking "do named theorems rank high?", score whole lemma libraries. A library S costs

  cost(S) = Σ_{v ∈ S} L(v) + Σ_{t ∈ library} L_S(t)

where each named lemma counts as one step once it is named, and L_S is the shortest proof when the lemmas in S are free. Every library has the same size as the human one (the 12 named candidates; 8 if only Principia's names are kept, since set.mm's were chosen in this exact axiom system). The score is the total saving over all 8,114 library theorems, so it no longer hangs on 12 labels.

| cost measure | greedy | top 12 by naming gain | human (12) | random, matched (mean / 95th pct) | human as % of greedy |
|---|---|---|---|---|---|
| tree size | 63,922 | 58,588 | 38,044 | 17,803 / 23,861 | 60% |
| DAG size | 20,375 | 16,099 | 9,900 | 5,040 / 7,152 | 49% |

Random libraries match the human one lemma for lemma in proof length and statement size (2,000 draws).

- **The human library beats every random library of the same shape** under both measures: about twice the matched-random saving. The Principia-only set does too (tree: 30,868 vs 10,649 mean; DAG: 7,664 vs 3,010).
- **Greedy does better, as it must.** It optimizes this exact number, while the humans also chose for proofs far beyond the 21-step horizon and for exposition. So the informative figure is the ratio: the human library gets 60% (tree) or 49% (DAG) of the greedy optimum, against about 25–28% for random.
- **Greedy and the humans agree at the top.** Greedy's first tree-size pick is Principia's *Syll* (`(p → q) → ((r → p) → (r → q))`, *2.05). Under DAG size it is second, and *2.75 is third. Two or three of greedy's 12 picks are human-named under either measure.
- Ranking candidates by naming gain alone gets 79–92% of greedy, so most of the contest is decided by individual gains, not by how lemmas combine.

### 2. Is tree size doing the work?

Under tree size, a lemma used m times in one proof is paid for m times, which flatters naming. Under DAG size each distinct step counts once. The smallest DAG proof is hard to find, so D(t) is computed by dynamic programming (each theorem keeps the smallest set of steps found; relaxed to a fixed point over the 21,241 theorems with L ≤ 17). That is an upper bound on the true smallest DAG. Total library cost drops from 128,820 (tree) to 79,592 (DAG).

| naming gain under | AUC | matched AUC (same size and proof length) |
|---|---|---|
| tree size | 0.92 (0.86–0.97) | 0.90 (0.78–0.99) |
| DAG size | 0.92 (0.87–0.96) | 0.79 (0.66–0.91) |

- **The effect survives, weaker.** Under DAG size, naming gain still separates named from unnamed theorems of the same size and proof length (interval clear of 0.5), but the matched AUC drops from 0.90 to 0.79. So part of the signal was the bookkeeping, and most of it was the lemmas.
- The two gains correlate at 0.88 (Spearman) over all 2,890 candidates. *Syll* stays near the top (rank 1 → 2).
- Lemmas whose value is mostly reuse inside one proof drop the most: `p → (q → (r → q))` (48 → 249), `(p → q) → ((q → r) → (p → r))` (22 → 176).

### Caveats

- Still one axiom system (ax-1..3) and a 21-step horizon. Humans named lemmas for long proofs this library can't see.
- DAG sizes are heuristic upper bounds. A better DAG solver could only lower DAG costs further.
- The price of a lemma is its proof from the axioms (L(v)), not from the lemmas already named. That's the simpler choice and slightly penalizes later picks.
