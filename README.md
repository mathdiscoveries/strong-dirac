# Strong Dirac Counterexamples (`n ≥ 8`) and Infinite Refutation of Grünbaum (2010)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490769.svg)](https://doi.org/10.5281/zenodo.24490769)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization in the Euclidean plane
$\mathbb{R}^2$ proving:

1. Every $n \ge 8$ admits a non-collinear $n$-point set with every point on at
   most $\lfloor n/2 \rfloor$ connecting lines (self-contained across all 12
   residue classes modulo 12, adapting Stefan Felsner's infinite $6K + 7$ family
   (as discussed by Grünbaum 2010 and reported in Brass, Moser, and Pach,
   *Research Problems in Discrete Geometry*, Springer 2005, p. 313) and adding an
   explicit 8-deletion
   construction for $n = 12k + 11$, $k \ge 2$).
2. Three infinite straight-line knight-lattice families with deficit $5/2$ below
   $n/2$: $n = 60s + 53$ and $n = 60s + 69$ ($s \ge 0$), and $n = 60s + 61$
   ($s \ge 1$), with exact maximum incidence $(n - 5)/2$.
3. Refutation of Grünbaum's 2010 conjecture $G(n) = 2\lfloor n/4 \rfloor$
   (*Geombinatorics* 20(2), 2010, 48–55) by at least $2$ across four infinite
   congruence classes modulo $60$.

## Provenance & Prior-Work Context

- **Akiyama, Ito, Kobayashi, and Nakamura (2011)**, *"Arrangements of $n$ Points
  whose Incident-Line-Numbers are at most $n/2$"*, *Graphs and Combinatorics*
  27(3) (2011), 321–326 (`doi:10.1007/s00373-011-1023-4`), covered 11 of 12
  residue classes modulo 12 (leaving $n = 12k + 11$, $k \ge 4$, open according
  to subsequent open surveys); pages 323–326 were paywalled and unread, and this
  formalization proves all 12 classes self-contained.
- **Companion paper & search logs** (the paper states and proves every
  compared statement; this package formalizes them):
  - https://mathdiscoveries.org/results/few-lines-through-every-point
  Logged literature searches (arXiv, CORE 2026-11-20, Google Scholar 2026-11-22,
  and open surveys by Lund–Purdy–Smith 2014, Trok 2020, Dumitrescu 2022, and
  Florek 2025) did not find prior constructions for $n = 12k + 11$ or infinite
  straight-line families with deficit $> 3/2$; paywalled pages of Akiyama et al.
  (2011) and print monographs remain unread/unsearched.

## Build & Verify

```bash
lake build Challenge Solution StrongDirac
lake env lean StrongDirac/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
