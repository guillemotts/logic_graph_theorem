# Lemma transfer: luk ↔ clav

A lemma is added as an extra axiom to a system and that system's library is regenerated (exact savings). Libraries: luk = `lukasiewicz`, 2893 theorems with L ≤ 15, clav = `clavius`, 5666 theorems with L ≤ 15.
Lemmas: from each system, its named candidates, its top 50 by naming gain and 300 sampled at random (701 in all).

## Does usefulness transfer?

Each lemma's saving at home and away, over the randomly sampled lemmas of each system (so the sample isn't biased toward good ones). Partial correlation removes the effect of statement size.

| lemmas from | sampled | Spearman home vs away | partial (size removed) | small statement vs away saving | no saving away | top-50 at home: median percentile away |
|---|---|---|---|---|---|---|
| luk (away = clav) | 300 | 0.20 | 0.02 | 0.44 | 78% | 39% (at home: 99%) |
| clav (away = luk) | 300 | 0.49 | 0.40 | 0.36 | 75% | 97% (at home: 99%) |

## Named lemmas from luk, tried in clav

12 named lemmas vs the random unnamed ones. Matched AUC compares each named lemma with unnamed ones of the same size and the same proof length in luk.

| saving measured in | AUC | matched AUC |
|---|---|---|
| luk | 0.92 (0.85–0.97) | 1.00 (1.00–1.00) |
| clav | 0.80 (0.66–0.92) | 0.42 (0.12–0.73) |

| lemma | names | saving in luk | saving in clav | percentile among random, in clav |
|---|---|---|---|---|
| `((p → q) → r) → (q → r)` | jarr | 1298 | 1128 | 100% |
| `p → (q → (r → q))` | ax1w | 1516 | 676 | 99% |
| `p → (q → (r → p))` | 2a1 | 2198 | 652 | 98% |
| `(p → q) → ((r → p) → (r → q))` | *1.6 Sum; *2.05 Syll; imim2 | 5154 | 616 | 98% |
| `p → p` | *2.08 Id; *2.11; *2.53; *2.54; id | 548 | 252 | 98% |
| `p → (q → q)` | idd | 526 | 252 | 98% |
| `p → ((p → q) → q)` | *2.25; *2.27; *2.55; pm2.27 | 1506 | 30 | 89% |
| `(p → q) → ((p → (q → r)) → (p → r))` | *2.75 | 2666 | 12 | 82% |
| `(p → (p → q)) → (p → q)` | *2.4; *2.43; pm2.43 | 722 | 6 | 80% |
| `¬p → (p → q)` | *2.21; pm2.21 | 342 | 0 | 39% |
| `(p → q) → ((q → r) → (p → r))` | *2.06 Syll; imim1 | 2908 | 0 | 39% |
| `p → (¬p → q)` | *2.2; *2.24; pm2.24 | 122 | 0 | 39% |

## The most useful lemmas in each system, and how they do in the other


### From luk

| lemma | named | saving in luk | saving in clav | percentile among random, in clav |
|---|---|---|---|---|
| `(p → q) → ((r → p) → (r → q))` | yes | 5154 | 616 | 98% |
| `p → ((q → (p → r)) → (q → r))` |  | 4962 | 582 | 98% |
| `(p → (q → r)) → (s → ((p → q) → (p → r)))` |  | 4086 | 20 | 84% |
| `(p → (q → r)) → ((s → (p → q)) → (s → (p → r)))` |  | 3306 | 0 | 39% |
| `(p → (q → r)) → (((p → q) → p) → ((p → q) → r))` |  | 3162 | 0 | 39% |
| `(p → (q → (r → s))) → (p → (t → ((q → r) → (q → s))))` |  | 3118 | 6 | 80% |
| `(p → (q → (r → s))) → ((p → q) → ((p → r) → (p → s)))` |  | 3068 | 0 | 39% |
| `(p → (q → r)) → ((p → q) → (s → (p → r)))` |  | 2942 | 592 | 98% |
| `((p → (q → r)) → (p → q)) → ((p → (q → r)) → (p → r))` |  | 2930 | 0 | 39% |
| `(p → q) → ((q → r) → (p → r))` | yes | 2908 | 0 | 39% |
| `(p → (q → r)) → (p → ((s → q) → (s → r)))` |  | 2846 | 366 | 98% |
| `p → ((¬q → ¬p) → q)` |  | 2802 | 30 | 89% |

### From clav

| lemma | named | saving in clav | saving in luk | percentile among random, in luk |
|---|---|---|---|---|
| `(p → q) → (((p → r) → s) → ((q → r) → s))` |  | 10956 | 1654 | 100% |
| `(p → q) → ((((q → r) → s) → t) → (((p → r) → s) → t))` |  | 9204 | 44 | 92% |
| `p → ((q → r) → (¬p → r))` |  | 8466 | 60 | 92% |
| `(p → q) → ((r → p) → ((q → s) → (r → s)))` |  | 8454 | 1014 | 100% |
| `p → (((¬p → q) → r) → ((s → q) → r))` |  | 7850 | 48 | 92% |
| `((((p → q) → r) → ((s → q) → r)) → t) → ((p → s) → t)` |  | 7484 | 76 | 94% |
| `(p → q) → (¬((q → r) → (p → r)) → s)` |  | 6930 | 322 | 99% |
| `(p → q) → ((¬p → p) → q)` |  | 6920 | 108 | 98% |
| `(((p → q) → (¬r → q)) → s) → (r → s)` |  | 6814 | 12 | 84% |
| `(((¬p → p) → q) → r) → ((p → q) → r)` |  | 6776 | 8 | 82% |
| `((p → q) → r) → (((¬p → s) → q) → r)` |  | 6374 | 158 | 99% |
| `(p → q) → ((((r → s) → (p → s)) → t) → ((q → r) → t))` |  | 6364 | 390 | 100% |
