# Strong Dirac Counterexamples (`n ≥ 8`) and Infinite Refutation of Grünbaum (2010)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization in the Euclidean plane
$\mathbb{R}^2$ proving:

1. Every $n \ge 8$ admits a non-collinear $n$-point set with every point on at
   most $\lfloor n/2 \rfloor$ connecting lines (self-contained across all 12
   residue classes modulo 12, closing $n = 12k + 11$).
2. Three infinite straight-line families with deficit $5/2$ below $n/2$:
   $n = 60s + 53$ and $n = 60s + 69$ ($s \ge 0$), and $n = 60s + 61$ ($s \ge 1$),
   with exact maximum incidence $(n - 5)/2$.
3. Refutation of Grünbaum's 2010 conjecture $G(n) = 2\lfloor n/4 \rfloor$ by at
   least $2$ across four infinite congruence classes modulo $60$.

## Build & Verify

```bash
lake build Challenge Solution StrongDirac
lake env lean StrongDirac/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
