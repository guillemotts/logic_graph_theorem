# Lemma contest: data/gen/luk21

Library: 8114 theorems. Candidates: 2890. Human set: the 12 named candidates (Principia-only subset: 8).

Saving = total proof length of the library without named lemmas, minus the cost with them (each named lemma paid for once). Higher is better.

| measure | baseline cost | greedy | top-k by gain | human | random (mean / 95th pct) | human beats random | human as % of greedy |
|---|---|---|---|---|---|---|---|
| tree | 128820 | 63922 | 58588 | 38044 | 17803 / 23861 | 100% | 60% |
| dag | 79592 | 20375 | 16099 | 9900 | 5040 / 7152 | 100% | 49% |

Principia-only human set (same contest, smaller k):

| measure | greedy (same k) | Principia set | random mean / 95th pct | Principia beats random |
|---|---|---|---|---|
| tree | 55424 | 30868 | 10649 / 17809 | 100% |
| dag | 16114 | 7664 | 3010 / 4565 | 100% |

## Greedy picks (tree)

1. `(p → q) → ((r → p) → (r → q))` (human-named)
2. `p → ((q → (p → r)) → (q → r))`
3. `p → ((¬q → ¬p) → q)`
4. `((p → (q → r)) → (p → q)) → ((p → (q → r)) → (p → r))`
5. `(p → (q → r)) → (((p → q) → p) → ((p → q) → r))`
6. `p → (q → (r → p))` (human-named)
7. `(p → (q → r)) → (s → ((p → q) → (p → r)))`
8. `(p → (q → (r → s))) → (p → ((q → r) → (q → s)))`
9. `(p → ((q → r) → q)) → ((p → (q → r)) → (p → r))`
10. `(p → (¬q → ¬r)) → (p → (r → q))`
11. `((¬p → ¬q) → q) → ((¬p → ¬q) → p)`
12. `(p → q) → (p → (r → q))`

## Greedy picks (dag)

1. `p → ((¬q → ¬p) → q)`
2. `(p → q) → ((r → p) → (r → q))` (human-named)
3. `(p → q) → ((p → (q → r)) → (p → r))` (human-named)
4. `((¬p → ¬q) → q) → ((¬p → ¬q) → p)`
5. `(p → q) → (((r → p) → r) → ((r → p) → q))`
6. `(p → (q → r)) → (s → ((p → q) → (p → r)))`
7. `(p → ((q → ((¬r → ¬s) → (s → r))) → t)) → (p → t)`
8. `(p → (q → (r → s))) → (p → ((q → r) → (q → s)))`
9. `(((p → (q → r)) → (p → q)) → (p → (q → r))) → (((p → (q → r)) → (p → q)) → (p → r))`
10. `p → (q → (r → p))` (human-named)
11. `((p → q) → ((p → p) → r)) → ((p → q) → r)`
12. `(p → q) → (p → (r → q))`

## Does naming gain pick out the human names under each measure?

| naming gain under | AUC | matched AUC (same size and proof length) |
|---|---|---|
| tree size | 0.92 (0.86–0.97) | 0.90 (0.78–0.99), 9 named |
| DAG size | 0.92 (0.87–0.96) | 0.79 (0.66–0.91), 9 named |

Spearman correlation between the two gains over all candidates: 0.880.

## Rank of each human lemma by naming gain

| lemma | tree rank | DAG rank |
|---|---|---|
| `p → (q → (r → q))` | 48 | 249 |
| `p → p` | 299 | 329 |
| `p → (q → q)` | 335 | 605 |
| `(p → (p → q)) → (p → q)` | 213 | 279 |
| `p → (q → (r → p))` | 20 | 138 |
| `(p → q) → ((r → p) → (r → q))` | 1 | 2 |
| `¬p → (p → q)` | 557 | 299 |
| `(p → q) → ((p → (q → r)) → (p → r))` | 10 | 7 |
| `((p → q) → r) → (q → r)` | 96 | 62 |
| `p → ((p → q) → q)` | 52 | 97 |
| `(p → q) → ((q → r) → (p → r))` | 22 | 176 |
| `p → (¬p → q)` | 1033 | 695 |
