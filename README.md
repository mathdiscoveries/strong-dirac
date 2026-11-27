# Planar Point Sets with at Most `⌊n/2⌋` Lines Through Every Point (`n ≥ 8`) and an Infinite Refutation of Grünbaum (2010)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490769.svg)](https://doi.org/10.5281/zenodo.24490769)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization in the Euclidean plane
$\mathbb{R}^2$ proving:

1. Every $n \ge 8$ admits a non-collinear $n$-point set with every point on at
   most $\lfloor n/2 \rfloor$ connecting lines (self-contained across all 12
   residue classes modulo 12, adapting Stefan Felsner's infinite $6K + 7$ family
   (Felsner, *Geometric Graphs and Arrangements*, Vieweg 2004, p. 86, as
   discussed by Grünbaum 2010 and reported in Brass, Moser, and Pach,
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
- **Felsner (2004)**, *Geometric Graphs and Arrangements*, p. 86: the source of
  the infinite $6K + 7$ family adapted here (`felsnerSet` and its 1-, 4- and
  8-deletions). The package gives explicit coordinates and Lean proofs for its
  1-, 4- and 8-deletions; Grünbaum (2010, p. 8) already lists single deletions
  of Felsner examples at $n = 42$ and $54$. Page 86 was not read; the
  attribution follows Grünbaum (2010) and Lund–Purdy–Smith (2014), both read.
- **Grünbaum (2009)**, *A catalogue of simplicial arrangements in the real
  projective plane*, *Ars Math. Contemp.* 2, 1–25: `h3Pts` is the dual of
  $A(15,1)$ (used at $n = 15$, and with one point deleted at $n = 14$) and
  `o23Pts` is $A(25,5)$ with two points deleted ($n = 23$); both match the
  catalogue's $f$-, $t$- and $r$-vectors.
- **Grünbaum (1972)**, *Arrangements and Spreads*, p. 25, and **Dirac (1951)**,
  *Collinearity properties of sets of points*, *Quart. J. Math.* 2, 221–227:
  earlier small counterexamples ($n = 9, 15, 19, 25, 31, 37$) and Dirac's
  even-$n$ configurations with $t = n/2$, which the all-$n$ theorem meets again
  at those sizes by its own constructions. Neither was read; both are recorded
  as background in `formalization.yaml`.
- **Companion paper & search logs** (the paper states and proves every
  compared statement; this package formalizes them):
  - https://mathdiscoveries.org/results/few-lines-through-every-point
  Logged literature searches (arXiv, CORE 2026-11-20, Google Scholar 2026-11-22,
  and open surveys by Lund–Purdy–Smith 2014, Trok 2020, Dumitrescu 2022, and
  Florek 2025) did not find prior constructions for $n = 12k + 11$ or infinite
  straight-line families with deficit $> 3/2$; paywalled pages of Akiyama et al.
  (2011) and print monographs remain unread/unsearched.

Coverage by this package's Palomar comparison: none of the companion paper's 7 main results is compared in Lean in full, and 3 are compared in part, all over the reals: Theorem 1 (the bound $\lfloor n/2 \rfloor$ for every $n \ge 8$ and its odd case, not the exact maximum $6j + 5$ of the rational grid $S_K$); Theorem 2 (5 of its 12 classes modulo 60: the odd classes 53, 9 and 1 with exact maximum $(n - 5)/2$, and the even classes 52 and 8 with an upper bound only); Proposition 3 (family A, without its rationality claim). This package's Lean library proves Theorems 1 and 2 and Proposition 3 as stated, with their rational configurations and exact maxima (StrongDirac.ExactEqualities: thm_half, thm_knights, familyA_odd_rational_exact), and Lemmas 4, 5, 6 and 7, but compares only the parts above; Conjecture 8 is open and not counted.

AI research agents built and directed by Tyler B. Hughes generated and checked this work. No human mathematician has yet refereed the proof.

## Build & Verify

```bash
lake build Challenge Solution StrongDirac
lake env lean StrongDirac/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
