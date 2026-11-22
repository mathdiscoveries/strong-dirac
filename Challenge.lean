module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Basic.Real.Basic

/-!
# Palomar Challenge: Strong Dirac Counterexamples (`n ≥ 8`) and Infinite Refutation of Grünbaum (2010)

For a finite set `P ⊂ ℝ²` of non-collinear points, let `lineCountR2 P a` be
the number of distinct Euclidean lines through `a` determined by `P`.

This challenge states six unconditional Euclidean theorems over `ℝ × ℝ`:
1. Every `n ≥ 8` admits a non-collinear `n`-point set with every point on at
   most `⌊n / 2⌋` connecting lines (`dirac_counterexample_all_ge_8`), and
   every odd `n ≥ 9` attains at most `(n - 1) / 2`.
2. Three infinite straight-line families with deficit `5 / 2` below `n / 2`:
   `n = 60s + 53` and `n = 60s + 69` for all `s ≥ 0` (exact maximum
   `30s + 24` and `30s + 32`), and `n = 60s + 61` for all `s ≥ 1` (exact
   maximum `30s + 28`).
3. Refutation of Grünbaum's 2010 conjecture `G(n) = 2 * ⌊n / 4⌋` by at least
   `2` for four infinite congruence classes modulo `60` (`s ≥ 0`).
-/

@[expose] public section

namespace StrongDiracChallenge

/-- Three points in `ℝ²` are collinear when their signed triangle area vanishes. -/
def CollinearR2 (a b c : ℝ × ℝ) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

/-- A finite point set in `ℝ²` is not all contained in a single line. -/
def NonCollinearR2 (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ CollinearR2 a b c

/-- The Euclidean line through `a` and `b` in `ℝ²`. -/
def lineR2 (a b : ℝ × ℝ) : Set (ℝ × ℝ) := {r : ℝ × ℝ | CollinearR2 a b r}

/-- The finite set of distinct connecting lines through `a` spanned by `P`. -/
noncomputable def spannedLinesR2 (P : Finset (ℝ × ℝ)) (a : ℝ × ℝ) : Finset (Set (ℝ × ℝ)) := by
  classical
  exact (P.erase a).image (lineR2 a)

/-- The exact number of connecting lines through `a` spanned by `P`. -/
noncomputable def lineCountR2 (P : Finset (ℝ × ℝ)) (a : ℝ × ℝ) : ℕ :=
  (spannedLinesR2 P a).card

/-- Grünbaum's 2010 conjectured lower bound `G(n) = 2 * ⌊n / 4⌋`. -/
def grunbaumVal (n : ℕ) : ℕ := 2 * (n / 4)

/-- Every `n ≥ 8` admits a non-collinear `n`-point set in `ℝ²` with every point
on at most `⌊n / 2⌋` connecting lines. -/
theorem dirac_counterexample_all_ge_8 (n : ℕ) (hn : 8 ≤ n) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ n / 2 := by
  sorry

/-- Every odd `n ≥ 9` admits a non-collinear `n`-point set in `ℝ²` with every
point on at most `(n - 1) / 2` connecting lines. -/
theorem dirac_counterexample_all_odd_ge_9 (n : ℕ) (hn : 9 ≤ n) (hodd : Odd n) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ (n - 1) / 2 := by
  sorry

/-- Infinite deficit-`5/2` family (`n = 60s + 53`, all `s ≥ 0`), exact maximum
`30s + 24 = (n - 5) / 2`. -/
theorem familyA_deficit_five_halves (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 53 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 24) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 24) := by
  sorry

/-- Infinite deficit-`5/2` family (`n = 60s + 69`, all `s ≥ 0`), exact maximum
`30s + 32 = (n - 5) / 2`. -/
theorem familyB_deficit_five_halves (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 69 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 32) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 32) := by
  sorry

/-- Third infinite deficit-`5/2` family (`n = 60s + 61`, all `s ≥ 1`), exact
maximum `30s + 28 = (n - 5) / 2`. -/
theorem familyC_deficit_five_halves {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 61 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 28) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 28) := by
  sorry

/-- Infinite refutation of Grünbaum's 2010 conjecture by at least `2` across
four congruence classes modulo `60` (`s ≥ 0`). -/
theorem refutes_grunbaum_2010 (s : ℕ) :
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 53 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 52 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 69 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 68 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) := by
  sorry

end StrongDiracChallenge
