/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Basic.Real.Basic
public import StrongDirac

/-!
# Palomar Solution: At Most `⌊n/2⌋` Lines Through Every Point (`n ≥ 8`) and an Infinite Refutation of Grünbaum (2010)
-/

@[expose] public section

namespace StrongDiracChallenge

def CollinearR2 (a b c : ℝ × ℝ) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

def NonCollinearR2 (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ CollinearR2 a b c

def lineR2 (a b : ℝ × ℝ) : Set (ℝ × ℝ) := {r : ℝ × ℝ | CollinearR2 a b r}

noncomputable def spannedLinesR2 (P : Finset (ℝ × ℝ)) (a : ℝ × ℝ) : Finset (Set (ℝ × ℝ)) := by
  classical
  exact (P.erase a).image (lineR2 a)

noncomputable def lineCountR2 (P : Finset (ℝ × ℝ)) (a : ℝ × ℝ) : ℕ :=
  (spannedLinesR2 P a).card

def grunbaumVal (n : ℕ) : ℕ := 2 * (n / 4)

theorem dirac_counterexample_all_ge_8 (n : ℕ) (hn : 8 ≤ n) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ n / 2 :=
  StrongDirac.TightnessAndMod12.dirac_counterexample_all_ge_8 n hn

theorem dirac_counterexample_all_odd_ge_9 (n : ℕ) (hn : 9 ≤ n) (hodd : Odd n) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ (n - 1) / 2 :=
  StrongDirac.TightnessAndMod12.dirac_counterexample_all_odd_ge_9 n hn hodd

theorem familyA_deficit_five_halves (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 53 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 24) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 24) :=
  StrongDirac.R17.r17_2_1_familyA_euclidean s

theorem familyB_deficit_five_halves (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 69 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 32) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 32) :=
  StrongDirac.R17.r17_2_1_familyB_euclidean s

theorem familyC_deficit_five_halves {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 61 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 28) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 28) :=
  StrongDirac.TightnessAndMod12.r17_2_3_familyC_euclidean hs

theorem refutes_grunbaum_2010 (s : ℕ) :
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 53 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 52 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 69 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 68 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) :=
  StrongDirac.R17.r17_2_1_refutes_grunbaum s

end StrongDiracChallenge
