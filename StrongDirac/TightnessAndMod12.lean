module

public import StrongDirac.Projective
public import StrongDirac.Class12kPlus11
public import StrongDirac.HullCert
public import StrongDirac.DeficitFiveHalves
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-!
# Tightness, All-`n ≥ 8` Mod-12 Dirac Counterexamples, and 12-Class Mod-60 Grünbaum Refutation

Extends `StrongDirac` unconditionally (zero `sorry`, zero `native_decide`, standard 3 axioms only):
1. **Target A (`12j+11 family` Exact Tightness & Closing `j = 0, 1`)**:
   - Exact tightness `projLineCount (S_K j) (1, 0, -Kval j) = 6 * j + 5` for all `j ≥ 2`,
     and Euclidean exact tightness `class12j11_euclidean_tight`.
   - Quadratic-ring projective-to-Euclidean lift (`ℤ[φ]` and `ℤ[√2]`), closing `j = 0`
     (`n = 11`, regular pentagon sides + diagonals + `ℓ_∞`, `t ≤ 5`) and `j = 1`
     (`n = 23`, octagon set `O25` minus 2 points, `t ≤ 10 ≤ 11`), giving
     `class12j11_all_j_euclidean` for every `j : ℕ`.
2. **Target B (Self-Contained All-`n ≥ 8` Mod-12 Theorem)**:
   - Formalizes the 4-direction square grid `sqGrid a` (`n = 4a + 5` and `4a + 4`, all
     `n ≡ 0, 1, 4, 5, 8, 9 (mod 12)` for `n ≥ 8`), Felsner's deficit-`3/2` family
     `felsnerSet k` (`n = 12k + 7` and `12k + 6` for `k ≥ 1`), the 4-deletion Felsner family
     `felsnerDel4 k` (`n = 12k + 3` and `12k + 2` for `k ≥ 3`), and combines them with
     `12j+11 family` (`12j + 11` and `12j + 10`) plus finite witnesses below `38` to prove
     `dirac_counterexample_all_ge_8` for EVERY `n ≥ 8` without external citations.
3. **Target C (12-Class Mod-60 Refutation of Grünbaum's 2010 Conjecture)**:
   - Proves `Family C` Family C (`B \ D_8`, `n = 60s + 61`, exact `t = 30s + 28 = G(n) - 2`
     for all `s ≥ 1`, refuting Grünbaum by `2` in all 6 even-half mod-12 classes
     `n ≡ 0, 1, 8, 9, 52, 53 (mod 60)`).
   - Proves `Family E4` Family E4 (`B \ D_4`, `n = 60s + 65`, `t ≤ 30s + 31 = G(n) - 1` for
     all `s ≥ 1`) and two new knight-lattice deletion families `A \ D_8` (`n = 60s + 45`,
     `t ≤ 30s + 21 = G(n) - 1`) and `A \ D_4` (`n = 60s + 49`, `t ≤ 30s + 23 = G(n) - 1`)
     for all `s ≥ 2`, refuting Grünbaum across **12 residue classes mod 60**
     (`6` by at least `2` and `6` more by at least `1`).
-/

@[expose] public section

namespace StrongDirac

namespace TightnessAndMod12

open StrongDirac.Class12kPlus11 StrongDirac.HullCert StrongDirac.DeficitFiveHalves

/-! ### Section 1: Subset Monotonicity, Ordinary-Line Deletion, and Quadratic-Field Lift -/

lemma proper_subset {X Y : Finset Pt} (hY : Proper Y) (hsub : X ⊆ Y) : Proper X :=
  ⟨fun p hp => hY.1 p (hsub hp),
   fun p hp q hq => hY.2 p (hsub hp) q (hsub hq)⟩

lemma projLineCount_subset_le {X Y : Finset Pt} (hsub : X ⊆ Y) (p : Pt) :
    projLineCount X p ≤ projLineCount Y p := by
  classical
  refine Finset.card_le_card (Finset.image_subset_image ?_)
  intro r hr
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1,
    hsub (Finset.mem_of_mem_erase hr)⟩

/-- `p` and `q` span an **ordinary line** of `X`: no third point of `X` is collinear with them. -/
def IsOrdinaryLine (X : Finset Pt) (p q : Pt) : Prop :=
  ∀ r ∈ X, det p q r = 0 → r = p ∨ r = q

/-- **Ordinary-Line Deletion Lemma**: if `W ⊆ D ∩ X.erase p` consists of deleted points each
forming an ordinary line of `X` with `p`, then deleting `D` reduces `projLineCount` at `p`
by at least `W.card`. -/
theorem projLineCount_sdiff_le_sub {X D W : Finset Pt} {p : Pt}
    (hX : Proper X) (hp : p ∈ X)
    (hWD : W ⊆ D) (hWX : W ⊆ X.erase p)
    (hord : ∀ q ∈ W, IsOrdinaryLine X p q) :
    projLineCount (X \ D) p + W.card ≤ projLineCount X p := by
  classical
  let Ssub : Finset (Set Pt) := spannedProjLines (X \ D) p
  let Swit : Finset (Set Pt) := W.image (projLine p)
  have hdisj : Disjoint Ssub Swit := by
    rw [Finset.disjoint_left]
    intro l hl1 hl2
    simp only [Ssub, spannedProjLines, Finset.mem_image, Finset.mem_erase,
      Finset.mem_sdiff] at hl1
    simp only [Swit, Finset.mem_image] at hl2
    rcases hl1 with ⟨r, ⟨hrne, hrX, hrnD⟩, rfl⟩
    rcases hl2 with ⟨q, hqW, heq⟩
    have hqX : q ∈ X := Finset.mem_of_mem_erase (hWX hqW)
    have hqne : q ≠ p := (Finset.mem_erase.mp (hWX hqW)).1
    have hns_q : ¬ SamePt p q := fun hs => hqne (hX.2 p hp q hqX hs).symm
    have hns_r : ¬ SamePt p r := fun hs => hrne (hX.2 p hp r hrX hs).symm
    have hdet : det p q r = 0 :=
      (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 q hqX) (hX.1 r hrX) hns_q hns_r).mp heq
    rcases hord q hqW r hrX hdet with rfl | rfl
    · exact hrne rfl
    · exact hrnD (hWD hqW)
  have hunion : Ssub ∪ Swit ⊆ spannedProjLines X p := by
    intro l hl
    rcases Finset.mem_union.mp hl with hl1 | hl2
    · simp only [Ssub, spannedProjLines, Finset.mem_image, Finset.mem_erase,
        Finset.mem_sdiff] at hl1 ⊢
      rcases hl1 with ⟨r, ⟨hrne, hrX, _⟩, rfl⟩
      exact ⟨r, ⟨hrne, hrX⟩, rfl⟩
    · simp only [Swit, spannedProjLines, Finset.mem_image] at hl2 ⊢
      rcases hl2 with ⟨q, hqW, rfl⟩
      exact ⟨q, hWX hqW, rfl⟩
  have hcardW : Swit.card = W.card := by
    refine Finset.card_image_of_injOn ?_
    intro q₁ hq₁ q₂ hq₂ heq
    by_contra hne
    have hq₁X : q₁ ∈ X := Finset.mem_of_mem_erase (hWX hq₁)
    have hq₂X : q₂ ∈ X := Finset.mem_of_mem_erase (hWX hq₂)
    have hq₁ne : q₁ ≠ p := (Finset.mem_erase.mp (hWX hq₁)).1
    have hq₂ne : q₂ ≠ p := (Finset.mem_erase.mp (hWX hq₂)).1
    have hns₁ : ¬ SamePt p q₁ := fun hs => hq₁ne (hX.2 p hp q₁ hq₁X hs).symm
    have hns₂ : ¬ SamePt p q₂ := fun hs => hq₂ne (hX.2 p hp q₂ hq₂X hs).symm
    have hdet : det p q₁ q₂ = 0 :=
      (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 q₁ hq₁X) (hX.1 q₂ hq₂X) hns₁ hns₂).mp heq
    rcases hord q₁ hq₁ q₂ hq₂X hdet with rfl | rfl
    · exact hq₂ne rfl
    · exact hne rfl
  have hle := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, hcardW] at hle
  exact hle

/-- Deleting one point `q ∈ X` from a `Proper` set while preserving a non-collinear triple
lifts to a Euclidean `ℝ²` point set of size `n` with the same upper bound `B`. -/
theorem exists_euclidean_erase_one {X : Finset Pt} {n B : ℕ} {q : Pt}
    (hX : Proper X) (hcard : X.card = n + 1) (hq : q ∈ X)
    (hnc : NonCollinear (X.erase q))
    (hbound : ∀ p ∈ X, projLineCount X p ≤ B) :
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ B := by
  have hsub : X.erase q ⊆ X := Finset.erase_subset q X
  have hcard' : (X.erase q).card = n := by
    rw [Finset.card_erase_of_mem hq, hcard]; omega
  refine exists_euclidean_set_le (proper_subset hX hsub) hcard' hnc ?_
  intro p hp
  exact (projLineCount_erase_le X p q).trans (hbound p (hsub hp))

/-! #### Quadratic Integer Rings `ℤ[α]` (`α² = a·α + b`, `α` irrational) & `ℝ²` Lift -/

/-- Element `u.1 + u.2 * α` of a quadratic integer ring `ℤ[α]` with `α² = a * α + b`. -/
abbrev QInt : Type := ℤ × ℤ

/-- Homogeneous projective triple over `ℤ[α]`. -/
abbrev QPt : Type := QInt × QInt × QInt

def qZero : QInt := (0, 0)
def qAdd (u v : QInt) : QInt := (u.1 + v.1, u.2 + v.2)
def qSub (u v : QInt) : QInt := (u.1 - v.1, u.2 - v.2)
def qMul (a b : ℤ) (u v : QInt) : QInt :=
  (u.1 * v.1 + b * u.2 * v.2, u.1 * v.2 + u.2 * v.1 + a * u.2 * v.2)

def qEval (α : ℝ) (u : QInt) : ℝ := (u.1 : ℝ) + (u.2 : ℝ) * α

def qCross (a b : ℤ) (p q : QPt) : QPt :=
  (qSub (qMul a b p.2.1 q.2.2) (qMul a b p.2.2 q.2.1),
   qSub (qMul a b p.2.2 q.1) (qMul a b p.1 q.2.2),
   qSub (qMul a b p.1 q.2.1) (qMul a b p.2.1 q.1))

def qDet (a b : ℤ) (p q r : QPt) : QInt :=
  let c1 := qSub (qMul a b q.2.1 r.2.2) (qMul a b q.2.2 r.2.1)
  let c2 := qSub (qMul a b q.1 r.2.2) (qMul a b q.2.2 r.1)
  let c3 := qSub (qMul a b q.1 r.2.1) (qMul a b q.2.1 r.1)
  qAdd (qSub (qMul a b p.1 c1) (qMul a b p.2.1 c2)) (qMul a b p.2.2 c3)

def qNonzero (p : QPt) : Bool :=
  p.1 != qZero || p.2.1 != qZero || p.2.2 != qZero

/-- Embed an integer projective point `(x, y, z)` into `QPt`. -/
def ofIntPt (p : Pt) : QPt := ((p.1, 0), (p.2.1, 0), (p.2.2, 0))

/-- Real homogeneous triple. -/
abbrev PtR : Type := ℝ × ℝ × ℝ

def evalQPt (α : ℝ) (p : QPt) : PtR :=
  (qEval α p.1, qEval α p.2.1, qEval α p.2.2)

def detR (p q r : PtR) : ℝ :=
  p.1 * (q.2.1 * r.2.2 - q.2.2 * r.2.1) -
  p.2.1 * (q.1 * r.2.2 - q.2.2 * r.1) +
  p.2.2 * (q.1 * r.2.1 - q.2.1 * r.1)

def crossR (p q : PtR) : PtR :=
  (p.2.1 * q.2.2 - p.2.2 * q.2.1,
   p.2.2 * q.1 - p.1 * q.2.2,
   p.1 * q.2.1 - p.2.1 * q.1)

def denomR (t : ℝ) (p : PtR) : ℝ := p.1 + t * p.2.1 + t ^ 2 * p.2.2

noncomputable def projToR2R (t : ℝ) (p : PtR) : ℝ × ℝ :=
  (p.2.1 / denomR t p, p.2.2 / denomR t p)

lemma qEval_add (α : ℝ) (u v : QInt) :
    qEval α (qAdd u v) = qEval α u + qEval α v := by
  unfold qEval qAdd; push_cast; ring

lemma qEval_sub (α : ℝ) (u v : QInt) :
    qEval α (qSub u v) = qEval α u - qEval α v := by
  unfold qEval qSub; push_cast; ring

lemma qEval_mul {a b : ℤ} {α : ℝ} (hα : α ^ 2 = (a : ℝ) * α + (b : ℝ)) (u v : QInt) :
    qEval α (qMul a b u v) = qEval α u * qEval α v := by
  unfold qEval qMul
  push_cast
  linear_combination (u.2 : ℝ) * (v.2 : ℝ) * (-hα)

lemma qEval_det {a b : ℤ} {α : ℝ} (hα : α ^ 2 = (a : ℝ) * α + (b : ℝ)) (p q r : QPt) :
    qEval α (qDet a b p q r) = detR (evalQPt α p) (evalQPt α q) (evalQPt α r) := by
  unfold qDet detR evalQPt
  simp only [qEval_add, qEval_sub, qEval_mul hα]

lemma qEval_cross {a b : ℤ} {α : ℝ} (hα : α ^ 2 = (a : ℝ) * α + (b : ℝ)) (p q : QPt) :
    evalQPt α (qCross a b p q) = crossR (evalQPt α p) (evalQPt α q) := by
  unfold qCross crossR evalQPt
  simp only [qEval_sub, qEval_mul hα]

/-- Exact area identity for the real projective chart `projToR2R t`. -/
lemma area_projToR2R_mul_denoms (t : ℝ) {p q r : PtR}
    (hp : denomR t p ≠ 0) (hq : denomR t q ≠ 0) (hr : denomR t r ≠ 0) :
    (((projToR2R t q).1 - (projToR2R t p).1) * ((projToR2R t r).2 - (projToR2R t p).2) -
     ((projToR2R t q).2 - (projToR2R t p).2) * ((projToR2R t r).1 - (projToR2R t p).1)) *
      (denomR t p * denomR t q * denomR t r) = detR p q r := by
  have hp1 : (projToR2R t p).1 * denomR t p = p.2.1 := div_mul_cancel₀ _ hp
  have hp2 : (projToR2R t p).2 * denomR t p = p.2.2 := div_mul_cancel₀ _ hp
  have hq1 : (projToR2R t q).1 * denomR t q = q.2.1 := div_mul_cancel₀ _ hq
  have hq2 : (projToR2R t q).2 * denomR t q = q.2.2 := div_mul_cancel₀ _ hq
  have hr1 : (projToR2R t r).1 * denomR t r = r.2.1 := div_mul_cancel₀ _ hr
  have hr2 : (projToR2R t r).2 * denomR t r = r.2.2 := div_mul_cancel₀ _ hr
  have h1 : (((projToR2R t q).1 - (projToR2R t p).1) * ((projToR2R t r).2 - (projToR2R t p).2) -
      ((projToR2R t q).2 - (projToR2R t p).2) * ((projToR2R t r).1 - (projToR2R t p).1)) *
      (denomR t p * denomR t q * denomR t r) =
      denomR t p * (q.2.1 * r.2.2 - q.2.2 * r.2.1) -
      denomR t q * (p.2.1 * r.2.2 - p.2.2 * r.2.1) +
      denomR t r * (p.2.1 * q.2.2 - p.2.2 * q.2.1) := by
    calc (((projToR2R t q).1 - (projToR2R t p).1) * ((projToR2R t r).2 - (projToR2R t p).2) -
          ((projToR2R t q).2 - (projToR2R t p).2) * ((projToR2R t r).1 - (projToR2R t p).1)) *
          (denomR t p * denomR t q * denomR t r)
        = denomR t p * (((projToR2R t q).1 * denomR t q) * ((projToR2R t r).2 * denomR t r) -
                       ((projToR2R t q).2 * denomR t q) * ((projToR2R t r).1 * denomR t r)) -
          denomR t q * (((projToR2R t p).1 * denomR t p) * ((projToR2R t r).2 * denomR t r) -
                       ((projToR2R t p).2 * denomR t p) * ((projToR2R t r).1 * denomR t r)) +
          denomR t r * (((projToR2R t p).1 * denomR t p) * ((projToR2R t q).2 * denomR t q) -
                       ((projToR2R t p).2 * denomR t p) * ((projToR2R t q).1 * denomR t q)) := by ring
      _ = _ := by rw [hp1, hp2, hq1, hq2, hr1, hr2]
  rw [h1]
  unfold denomR detR
  ring

lemma collinearR2_projToR2R_iff (t : ℝ) {p q r : PtR}
    (hp : denomR t p ≠ 0) (hq : denomR t q ≠ 0) (hr : denomR t r ≠ 0) :
    CollinearR2 (projToR2R t p) (projToR2R t q) (projToR2R t r) ↔ detR p q r = 0 := by
  unfold CollinearR2
  have hden : denomR t p * denomR t q * denomR t r ≠ 0 := mul_ne_zero (mul_ne_zero hp hq) hr
  rw [← area_projToR2R_mul_denoms t hp hq hr, mul_eq_zero]
  simp only [hden, or_false]

lemma projToR2R_eq_imp_cross {t : ℝ} {p q : PtR}
    (hp : denomR t p ≠ 0) (hq : denomR t q ≠ 0)
    (heq : projToR2R t p = projToR2R t q) : crossR p q = (0, 0, 0) := by
  have hy : p.2.1 * denomR t q = q.2.1 * denomR t p :=
    (div_eq_div_iff hp hq).mp (congrArg Prod.fst heq)
  have hz : p.2.2 * denomR t q = q.2.2 * denomR t p :=
    (div_eq_div_iff hp hq).mp (congrArg Prod.snd heq)
  have hx : p.1 * denomR t q = q.1 * denomR t p := by
    have hp_eq : p.1 = denomR t p - t * p.2.1 - t ^ 2 * p.2.2 := by unfold denomR; ring
    have hq_eq : q.1 = denomR t q - t * q.2.1 - t ^ 2 * q.2.2 := by unfold denomR; ring
    linear_combination (denomR t q) * hp_eq - (denomR t p) * hq_eq - t * hy - t ^ 2 * hz
  have hc1 : p.2.1 * q.2.2 - p.2.2 * q.2.1 = 0 := by
    have hr : (p.2.1 * q.2.2 - p.2.2 * q.2.1) * denomR t p = 0 := by
      linear_combination -p.2.1 * hz + p.2.2 * hy
    exact (mul_eq_zero.mp hr).resolve_right hp
  have hc2 : p.2.2 * q.1 - p.1 * q.2.2 = 0 := by
    have hr : (p.2.2 * q.1 - p.1 * q.2.2) * denomR t p = 0 := by
      linear_combination -p.2.2 * hx + p.1 * hz
    exact (mul_eq_zero.mp hr).resolve_right hp
  have hc3 : p.1 * q.2.1 - p.2.1 * q.1 = 0 := by
    have hr : (p.1 * q.2.1 - p.2.1 * q.1) * denomR t p = 0 := by
      linear_combination -p.1 * hy + p.2.1 * hx
    exact (mul_eq_zero.mp hr).resolve_right hp
  exact Prod.ext hc1 (Prod.ext hc2 hc3)

lemma quadratic_roots_card_le_twoR {p : PtR} (hp : p ≠ (0, 0, 0)) (S : Finset ℕ) :
    (S.filter (fun k : ℕ => denomR (k : ℝ) p = 0)).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hgt
  have r1 : p.1 + (k₁ : ℝ) * p.2.1 + (k₁ : ℝ) ^ 2 * p.2.2 = 0 := (Finset.mem_filter.mp hk₁).2
  have r2 : p.1 + (k₂ : ℝ) * p.2.1 + (k₂ : ℝ) ^ 2 * p.2.2 = 0 := (Finset.mem_filter.mp hk₂).2
  have r3 : p.1 + (k₃ : ℝ) * p.2.1 + (k₃ : ℝ) ^ 2 * p.2.2 = 0 := (Finset.mem_filter.mp hk₃).2
  have d12 : (k₂ : ℝ) - (k₁ : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h12.symm)
  have d13 : (k₃ : ℝ) - (k₁ : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h13.symm)
  have d23 : (k₃ : ℝ) - (k₂ : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h23.symm)
  have e12 : p.2.1 + ((k₂ : ℝ) + (k₁ : ℝ)) * p.2.2 = 0 := by
    have hmul : ((k₂ : ℝ) - (k₁ : ℝ)) * (p.2.1 + ((k₂ : ℝ) + (k₁ : ℝ)) * p.2.2) = 0 := by
      linear_combination r2 - r1
    exact (mul_eq_zero.mp hmul).resolve_left d12
  have e13 : p.2.1 + ((k₃ : ℝ) + (k₁ : ℝ)) * p.2.2 = 0 := by
    have hmul : ((k₃ : ℝ) - (k₁ : ℝ)) * (p.2.1 + ((k₃ : ℝ) + (k₁ : ℝ)) * p.2.2) = 0 := by
      linear_combination r3 - r1
    exact (mul_eq_zero.mp hmul).resolve_left d13
  have hzR : p.2.2 = 0 := by
    have hmul : ((k₃ : ℝ) - (k₂ : ℝ)) * p.2.2 = 0 := by linear_combination e13 - e12
    exact (mul_eq_zero.mp hmul).resolve_left d23
  have hyR : p.2.1 = 0 := by linear_combination e12 - ((k₂ : ℝ) + (k₁ : ℝ)) * hzR
  have hxR : p.1 = 0 := by linear_combination r1 - (k₁ : ℝ) * hyR - (k₁ : ℝ) ^ 2 * hzR
  exact hp (Prod.ext hxR (Prod.ext hyR hzR))

lemma exists_good_paramR (S : Finset PtR) (hS : ∀ p ∈ S, p ≠ (0, 0, 0)) :
    ∃ t : ℝ, ∀ p ∈ S, denomR t p ≠ 0 := by
  classical
  let R : Finset ℕ := Finset.range (2 * S.card + 1)
  let zeros : Finset ℕ := S.biUnion (fun p => R.filter (fun k => denomR (k : ℝ) p = 0))
  have hzeros_card : zeros.card ≤ 2 * S.card := by
    calc zeros.card
        ≤ ∑ p ∈ S, (R.filter (fun k : ℕ => denomR (k : ℝ) p = 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ S, 2 := Finset.sum_le_sum (fun p hp => quadratic_roots_card_le_twoR (hS p hp) R)
      _ = 2 * S.card := by simp [mul_comm]
  have hlt : zeros.card < R.card := by rw [Finset.card_range]; omega
  obtain ⟨k, hkR, hkz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨(k : ℝ), fun p hp hzero => hkz ?_⟩
  exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hkR, hzero⟩⟩

/-- Deduplicate a list of `QPt` modulo collinearity through `p`, returning one representative
per spanned projective line through `p`. -/
def qLineReps (a b : ℤ) (p : QPt) : List QPt → List QPt
  | [] => []
  | q :: qs =>
      let rest := qLineReps a b p qs
      if rest.any (fun r => qDet a b p q r == qZero) then rest else q :: rest

/-- Pure-kernel computable checker for a finite projective set over `ℤ[α]` (`α² = a·α + b`):
verifies distinct nonzero projective points, non-collinearity, and `t(p) ≤ B` at every point. -/
def checkQSet (a b : ℤ) (pts : List QPt) (B : ℕ) : Bool :=
  pts.all qNonzero &&
  (pts.zipIdx.all fun (p, i) =>
    pts.zipIdx.all fun (q, j) =>
      i == j || qNonzero (qCross a b p q)) &&
  (pts.any fun p => pts.any fun q => pts.any fun r => qDet a b p q r != qZero) &&
  (pts.all fun p => (qLineReps a b p (pts.filter (fun q => q != p))).length ≤ B)

lemma qLineReps_subset {a b : ℤ} {p : QPt} {l : List QPt} :
    ∀ r ∈ qLineReps a b p l, r ∈ l := by
  induction l with
  | nil => simp [qLineReps]
  | cons q qs ih =>
    intro r hr
    simp only [qLineReps] at hr
    split at hr
    · exact List.mem_cons_of_mem q (ih r hr)
    · rcases List.mem_cons.mp hr with rfl | hmem
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem q (ih r hmem)

lemma qLineReps_covers {a b : ℤ} {p : QPt} {l : List QPt}
    (hself : ∀ q, qDet a b p q q = qZero) :
    ∀ q ∈ l, ∃ r ∈ qLineReps a b p l, qDet a b p q r = qZero := by
  induction l with
  | nil => intro q hq; cases hq
  | cons q₀ qs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hmem
    · simp only [qLineReps]
      split
      · rename_i h
        rw [List.any_eq_true] at h
        rcases h with ⟨r, hr, hdet⟩
        exact ⟨r, hr, beq_iff_eq.mp hdet⟩
      · exact ⟨q, List.mem_cons_self .., hself q⟩
    · rcases ih q hmem with ⟨r, hr, hdet⟩
      simp only [qLineReps]
      split
      · exact ⟨r, hr, hdet⟩
      · exact ⟨r, List.mem_cons_of_mem q₀ hr, hdet⟩

lemma qDet_self_right (a b : ℤ) (p q : QPt) : qDet a b p q q = qZero := by
  unfold qDet qZero qAdd qSub qMul
  refine Prod.ext ?_ ?_ <;> ring

/-- Soundness of `checkQSet`: any finite list passing `checkQSet a b pts B = true` over an
irrational quadratic `α ∈ ℝ` (`α² = a·α + b`) embeds into `ℝ × ℝ` with `P.card = pts.length`,
`NonCollinearR2 P`, and `∀ x ∈ P, lineCountR2 P x ≤ B`. -/
theorem exists_euclidean_of_checkQSet {a b : ℤ} {α : ℝ}
    (hα : α ^ 2 = (a : ℝ) * α + (b : ℝ))
    (hker : ∀ u : QInt, qEval α u = 0 → u = qZero)
    {pts : List QPt} {B : ℕ}
    (hchk : checkQSet a b pts B = true) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = pts.length ∧ NonCollinearR2 P ∧ ∀ x ∈ P, lineCountR2 P x ≤ B := by
  classical
  have h1 : pts.all qNonzero = true := by
    unfold checkQSet at hchk; simp only [Bool.and_eq_true] at hchk; exact hchk.1.1.1
  have h2 : (pts.zipIdx.all fun (p, i) =>
      pts.zipIdx.all fun (q, j) => i == j || qNonzero (qCross a b p q)) = true := by
    unfold checkQSet at hchk; simp only [Bool.and_eq_true] at hchk; exact hchk.1.1.2
  have h3 : (pts.any fun p => pts.any fun q => pts.any fun r => qDet a b p q r != qZero) = true := by
    unfold checkQSet at hchk; simp only [Bool.and_eq_true] at hchk; exact hchk.1.2
  have h4 : (pts.all fun p => (qLineReps a b p (pts.filter (fun q => q != p))).length ≤ B) = true := by
    unfold checkQSet at hchk; simp only [Bool.and_eq_true] at hchk; exact hchk.2
  have hqnz_iff : ∀ p : QPt, qNonzero p = true ↔ evalQPt α p ≠ (0, 0, 0) := by
    intro p
    unfold qNonzero evalQPt
    constructor
    · intro h heq
      have h1' := hker p.1 (congrArg Prod.fst heq)
      have h2' := hker p.2.1 (congrArg (fun x => x.2.1) heq)
      have h3' := hker p.2.2 (congrArg (fun x => x.2.2) heq)
      simp [h1', h2', h3'] at h
    · intro h
      by_contra hf
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hf
      rcases hf with ⟨⟨h1', h2'⟩, h3'⟩
      apply h
      simp [h1', h2', h3', qEval, qZero]
  have hnodup : pts.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    apply Fin.ext
    by_contra hne
    have hi' : (pts[i], i) ∈ pts.zipIdx := by
      have := List.getElem_mem (l := pts.zipIdx) (n := i) (by simp [hi])
      simpa [List.getElem_zipIdx] using this
    have hj' : (pts[j], j) ∈ pts.zipIdx := by
      have := List.getElem_mem (l := pts.zipIdx) (n := j) (by simp [hj])
      simpa [List.getElem_zipIdx] using this
    have hcr := (List.all_eq_true.mp ((List.all_eq_true.mp h2) _ hi')) _ hj'
    simp only [Bool.or_eq_true, beq_iff_eq] at hcr
    have hcr' : qNonzero (qCross a b pts[i] pts[j]) = true :=
      hcr.resolve_left hne
    simp only at heq
    rw [heq] at hcr'
    have hzero : evalQPt α (qCross a b pts[j] pts[j]) = (0, 0, 0) := by
      rw [qEval_cross hα]; unfold crossR; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring
    exact (hqnz_iff _).mp hcr' hzero
  have hpair_cross : ∀ p ∈ pts, ∀ q ∈ pts, p ≠ q →
      crossR (evalQPt α p) (evalQPt α q) ≠ (0, 0, 0) := by
    intro p hp q hq hne
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hij : i ≠ j := fun h => hne (by subst h; rfl)
    have hi' : (pts[i], i) ∈ pts.zipIdx := by
      have := List.getElem_mem (l := pts.zipIdx) (n := i) (by simp [hi])
      simpa [List.getElem_zipIdx] using this
    have hj' : (pts[j], j) ∈ pts.zipIdx := by
      have := List.getElem_mem (l := pts.zipIdx) (n := j) (by simp [hj])
      simpa [List.getElem_zipIdx] using this
    have hcr := (List.all_eq_true.mp ((List.all_eq_true.mp h2) _ hi')) _ hj'
    simp only [Bool.or_eq_true, beq_iff_eq] at hcr
    have hcr' : qNonzero (qCross a b pts[i] pts[j]) = true := hcr.resolve_left hij
    rw [← qEval_cross hα]
    exact (hqnz_iff _).mp hcr'
  let S : Finset PtR := (pts.map (evalQPt α)).toFinset
  have hSnz : ∀ v ∈ S, v ≠ (0, 0, 0) := by
    intro v hv
    simp only [S, List.mem_toFinset, List.mem_map] at hv
    rcases hv with ⟨p, hp, rfl⟩
    exact (hqnz_iff p).mp (List.all_eq_true.mp h1 p hp)
  obtain ⟨t, hden⟩ := exists_good_paramR S hSnz
  let φ : QPt → ℝ × ℝ := fun p => projToR2R t (evalQPt α p)
  have hden_p : ∀ p ∈ pts, denomR t (evalQPt α p) ≠ 0 :=
    fun p hp => hden _ (List.mem_toFinset.mpr (List.mem_map_of_mem hp))
  have hinj : ∀ p ∈ pts, ∀ q ∈ pts, φ p = φ q → p = q := by
    intro p hp q hq hφ
    by_contra hne
    have hc := projToR2R_eq_imp_cross (hden_p p hp) (hden_p q hq) hφ
    exact hpair_cross p hp q hq hne hc
  let P : Finset (ℝ × ℝ) := pts.toFinset.image φ
  have hPcard : P.card = pts.length := by
    rw [Finset.card_image_of_injOn (fun p hp q hq h =>
      hinj p (List.mem_toFinset.mp hp) q (List.mem_toFinset.mp hq) h),
      List.toFinset_card_of_nodup hnodup]
  have hPnc : NonCollinearR2 P := by
    simp only [List.any_eq_true, bne_iff_ne] at h3
    rcases h3 with ⟨p, hp, q, hq, r, hr, hdet⟩
    refine ⟨φ p, Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hp),
            φ q, Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hq),
            φ r, Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hr), ?_⟩
    rw [collinearR2_projToR2R_iff t (hden_p p hp) (hden_p q hq) (hden_p r hr)]
    intro h0
    rw [← qEval_det hα] at h0
    exact hdet (hker _ h0)
  refine ⟨P, hPcard, hPnc, ?_⟩
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨p, hp', rfl⟩
  have hp : p ∈ pts := List.mem_toFinset.mp hp'
  let reps : List QPt := qLineReps a b p (pts.filter (fun q => q != p))
  have hreps_len : reps.length ≤ B :=
    decide_eq_true_eq.mp (List.all_eq_true.mp h4 p hp)
  have hsub : spannedLinesR2 P (φ p) ⊆ reps.toFinset.image (fun r => lineR2 (φ p) (φ r)) := by
    intro l hl
    simp only [spannedLinesR2, Finset.mem_image, Finset.mem_erase] at hl
    rcases hl with ⟨y, ⟨hyne, hyP⟩, rfl⟩
    rcases Finset.mem_image.mp hyP with ⟨q, hq', rfl⟩
    have hq : q ∈ pts := List.mem_toFinset.mp hq'
    have hqp : q ≠ p := fun h => hyne (by rw [h])
    have hqfilt : q ∈ pts.filter (fun q => q != p) :=
      List.mem_filter.mpr ⟨hq, bne_iff_ne.mpr hqp⟩
    obtain ⟨r, hr, hdet0⟩ := qLineReps_covers (qDet_self_right a b p) q hqfilt
    have hrfilt := qLineReps_subset r hr
    have hrpts : r ∈ pts := (List.mem_filter.mp hrfilt).1
    have hrne : r ≠ p := bne_iff_ne.mp (List.mem_filter.mp hrfilt).2
    have hφr : φ p ≠ φ r := fun h => hrne (hinj p hp r hrpts h).symm
    have hφq : φ p ≠ φ q := fun h => hqp (hinj p hp q hq h).symm
    have hdetR : detR (evalQPt α p) (evalQPt α q) (evalQPt α r) = 0 := by
      rw [← qEval_det hα, hdet0]; simp [qEval, qZero]
    have hcol : CollinearR2 (φ p) (φ q) (φ r) :=
      (collinearR2_projToR2R_iff t (hden_p p hp) (hden_p q hq) (hden_p r hrpts)).mpr hdetR
    have hleq : lineR2 (φ p) (φ q) = lineR2 (φ p) (φ r) :=
      (lineR2_eq_iff_collinearR2 hφq hφr).mpr hcol
    rw [hleq]
    exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hr)
  calc lineCountR2 P (φ p)
      = (spannedLinesR2 P (φ p)).card := rfl
    _ ≤ (reps.toFinset.image (fun r => lineR2 (φ p) (φ r))).card := Finset.card_le_card hsub
    _ ≤ reps.toFinset.card := Finset.card_image_le
    _ ≤ reps.length := List.toFinset_card_le reps
    _ ≤ B := hreps_len

/-- Elementary irrationality kernel for `√2`: `u.1 + u.2 * √2 = 0 → u = (0, 0)`. -/
lemma sqrt2_ker (u : QInt) (h : qEval (Real.sqrt 2) u = 0) : u = qZero := by
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmul : (((u.1 ^ 2 : ℤ) : ℝ)) = (((2 * u.2 ^ 2 : ℤ) : ℝ)) := by
    have h1 : (u.1 : ℝ) = -(u.2 : ℝ) * Real.sqrt 2 := by
      unfold qEval at h; linarith
    push_cast
    calc (u.1 : ℝ) ^ 2 = (-(u.2 : ℝ) * Real.sqrt 2) ^ 2 := by rw [h1]
      _ = (u.2 : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = 2 * (u.2 : ℝ) ^ 2 := by rw [hsq2]; ring
  have hint : u.1 ^ 2 = 2 * u.2 ^ 2 := Int.cast_injective hmul
  have hnat : u.1.natAbs ^ 2 = 2 * u.2.natAbs ^ 2 := by
    have := congrArg Int.natAbs hint
    simpa [Int.natAbs_mul, pow_two] using this
  have hzero : ∀ a b : ℕ, a ^ 2 = 2 * b ^ 2 → a = 0 ∧ b = 0 := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro b hab
      by_cases ha : a = 0
      · subst ha
        have hb0 : b * b = 0 := by nlinarith
        exact ⟨rfl, mul_self_eq_zero.mp hb0⟩
      · have ha_even : 2 ∣ a := by
          by_contra hodd
          have h1 : a % 2 = 1 := by omega
          have h2 : a ^ 2 % 2 = 1 := by rw [pow_two, Nat.mul_mod, h1]
          omega
        rcases ha_even with ⟨a', rfl⟩
        have hb2 : b ^ 2 = 2 * a' ^ 2 := by
          have : 4 * a' ^ 2 = 2 * b ^ 2 := by linarith
          omega
        have hb_even : 2 ∣ b := by
          by_contra hodd
          have h1 : b % 2 = 1 := by omega
          have h2 : b ^ 2 % 2 = 1 := by rw [pow_two, Nat.mul_mod, h1]
          omega
        rcases hb_even with ⟨b', rfl⟩
        have hrec : a' ^ 2 = 2 * b' ^ 2 := by
          have : 4 * b' ^ 2 = 2 * a' ^ 2 := by linarith
          omega
        have hlt : a' < 2 * a' := by omega
        obtain ⟨ha0, _⟩ := ih a' hlt b' hrec
        omega
  obtain ⟨h1, h2⟩ := hzero u.1.natAbs u.2.natAbs hnat
  exact Prod.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2)

/-- Elementary irrationality kernel for `φ = (1 + √5) / 2`: `u.1 + u.2 * φ = 0 → u = (0, 0)`. -/
lemma phi_ker (u : QInt) (h : qEval ((1 + Real.sqrt 5) / 2) u = 0) : u = qZero := by
  have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h1 : (2 * (u.1 : ℝ) + (u.2 : ℝ)) = -(u.2 : ℝ) * Real.sqrt 5 := by
    unfold qEval at h; linarith
  have hmul : (((2 * u.1 + u.2) ^ 2 : ℤ) : ℝ) = ((5 * u.2 ^ 2 : ℤ) : ℝ) := by
    push_cast
    calc (2 * (u.1 : ℝ) + (u.2 : ℝ)) ^ 2 = (-(u.2 : ℝ) * Real.sqrt 5) ^ 2 := by rw [h1]
      _ = (u.2 : ℝ) ^ 2 * (Real.sqrt 5) ^ 2 := by ring
      _ = 5 * (u.2 : ℝ) ^ 2 := by rw [hsq5]; ring
  have hint : (2 * u.1 + u.2) ^ 2 = 5 * u.2 ^ 2 := Int.cast_injective hmul
  have hnat : (2 * u.1 + u.2).natAbs ^ 2 = 5 * u.2.natAbs ^ 2 := by
    have := congrArg Int.natAbs hint
    simpa [Int.natAbs_mul, pow_two] using this
  have hzero : ∀ a b : ℕ, a ^ 2 = 5 * b ^ 2 → a = 0 ∧ b = 0 := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro b hab
      by_cases ha : a = 0
      · subst ha
        have hb0 : b * b = 0 := by nlinarith
        exact ⟨rfl, mul_self_eq_zero.mp hb0⟩
      · have h5div : ∀ x y : ℕ, x ^ 2 = 5 * y ^ 2 → 5 ∣ x := by
          intro x y hxy
          have hm : (x % 5) * (x % 5) % 5 = 0 := by
            rw [← Nat.mul_mod, ← pow_two, hxy]; omega
          have hlt5 : x % 5 < 5 := Nat.mod_lt x (by omega)
          have hmod0 : x % 5 = 0 := by
            have : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
            rcases this with h' | h' | h' | h' | h' <;> simp [h'] at hm ⊢
          exact Nat.dvd_of_mod_eq_zero hmod0
        rcases h5div a b hab with ⟨a', rfl⟩
        have hb2 : b ^ 2 = 5 * a' ^ 2 := by
          have : 25 * a' ^ 2 = 5 * b ^ 2 := by linarith
          omega
        rcases h5div b a' hb2 with ⟨b', rfl⟩
        have hrec : a' ^ 2 = 5 * b' ^ 2 := by
          have : 25 * b' ^ 2 = 5 * a' ^ 2 := by linarith
          omega
        have hlt : a' < 5 * a' := by omega
        obtain ⟨ha0, _⟩ := ih a' hlt b' hrec
        omega
  obtain ⟨h1', h2'⟩ := hzero (2 * u.1 + u.2).natAbs u.2.natAbs hnat
  have hu2 : u.2 = 0 := Int.natAbs_eq_zero.mp h2'
  have hu12 : 2 * u.1 + u.2 = 0 := Int.natAbs_eq_zero.mp h1'
  unfold qZero
  exact Prod.ext (by omega) hu2

lemma phi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 : ℤ) * ((1 + Real.sqrt 5) / 2) + (1 : ℤ) := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  push_cast
  linear_combination h5 / 4

lemma sqrt2_sq : (Real.sqrt 2) ^ 2 = (0 : ℤ) * Real.sqrt 2 + (2 : ℤ) := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast
  linarith

/-! ### Section 2: Target A — `12j+11 family` Exact Tightness (`j ≥ 2`) and Closing `j = 0, 1` -/

/-- Exact tightness witness for `S_K j` (`j ≥ 2`) at `(1, 0, -Kval j)`:
`projLineCount (S_K j) (1, 0, -Kval j) = 6 * j + 5`. -/
theorem S_K_top_lineCount {j : ℕ} (hj : 2 ≤ j) :
    projLineCount (S_K j) (1, 0, -Kval j) = 6 * j + 5 := by
  set K := Kval j
  have hK : 6 ≤ K := by unfold K Kval; omega
  have hKJ : K ∈ Jset K := mem_Jset_iff.mpr (by omega)
  have hp : (1, 0, -K) ∈ S_K j := mem_S_K_iff.mpr (Or.inl ⟨K, hKJ, rfl⟩)
  have hle : projLineCount (S_K j) (1, 0, -K) ≤ 6 * j + 5 := S_K_lineCount_le hj _ hp
  let W1 : Finset Pt := {(0, 0, 1)}
  let W2 : Finset Pt := (Jset K).image (fun y => (0, 1, -y))
  let R3 : Finset ℤ := (Finset.Icc (-2 * K) (-K - 1)).erase (1 - 2 * K)
  let W3 : Finset Pt := R3.image (fun y => (1, 1, -(K + y)))
  let W4 : Finset Pt := {(1, 1, -1)}
  let W : Finset Pt := W1 ∪ W2 ∪ W3 ∪ W4
  have hW_sub : W ⊆ (S_K j).erase (1, 0, -K) := by
    intro q hq
    simp only [W, W1, W2, W3, W4, R3, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_erase, Finset.mem_Icc] at hq
    rw [Finset.mem_erase]
    rcases hq with ((rfl | ⟨y, hy, rfl⟩) | ⟨y, ⟨hyne, hylo, hyhi⟩, rfl⟩) | rfl
    · refine ⟨by simp, mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))⟩
    · refine ⟨by simp, mem_S_K_iff.mpr (Or.inr (Or.inl ⟨y, hy, rfl⟩))⟩
    · refine ⟨by simp, mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inl ⟨K + y, ?_, rfl⟩)))⟩
      exact mem_JZset_iff.mpr (by omega)
    · refine ⟨by simp, mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inl ⟨1, ?_, rfl⟩)))⟩
      exact mem_JZset_iff.mpr (by omega)
  have hW_wit : ∀ q₁ ∈ W, ∀ q₂ ∈ W, q₁ ≠ q₂ → det (1, 0, -K) q₁ q₂ ≠ 0 := by
    intro q₁ hq₁ q₂ hq₂ hne hdet
    simp only [W, W1, W2, W3, W4, R3, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_erase, Finset.mem_Icc] at hq₁ hq₂
    rcases hq₁ with ((rfl | ⟨y₁, hy₁, rfl⟩) | ⟨y₁, ⟨_, hlo₁, hhi₁⟩, rfl⟩) | rfl <;>
    rcases hq₂ with ((rfl | ⟨y₂, hy₂, rfl⟩) | ⟨y₂, ⟨_, hlo₂, hhi₂⟩, rfl⟩) | rfl <;>
    unfold det at hdet <;>
    simp only at hdet
    all_goals try exact hne rfl
    all_goals try omega
    · exact hne (by congr 2; omega)
    · rw [mem_Jset_iff] at hy₁; omega
    · rw [mem_Jset_iff] at hy₁; omega
    · rw [mem_Jset_iff] at hy₂; omega
    · exact hne (by congr 2; omega)
    · rw [mem_Jset_iff] at hy₂; omega
  have hcard1 : W1.card = 1 := Finset.card_singleton _
  have hcard2 : W2.card = 4 * j + 2 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simp at h; exact h), card_Jset hj]
  have hcard3 : W3.card = 2 * j + 1 := by
    have hmem : 1 - 2 * K ∈ Finset.Icc (-2 * K) (-K - 1) := Finset.mem_Icc.mpr (by omega)
    rw [Finset.card_image_of_injective _ (fun a b h => by simp at h; omega),
      Finset.card_erase_of_mem hmem, Int.card_Icc]
    unfold K Kval; omega
  have hcard4 : W4.card = 1 := Finset.card_singleton _
  have hd12 : Disjoint W1 W2 := by
    rw [Finset.disjoint_left]; intro q h1 h2
    simp only [W1, W2, Finset.mem_singleton, Finset.mem_image] at h1 h2
    subst h1; rcases h2 with ⟨_, _, h⟩; simp at h
  have hd123 : Disjoint (W1 ∪ W2) W3 := by
    rw [Finset.disjoint_left]; intro q h12 h3
    simp only [W1, W2, W3, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at h12 h3
    rcases h3 with ⟨_, _, rfl⟩
    rcases h12 with h | ⟨_, _, h⟩ <;> simp at h
  have hd1234 : Disjoint (W1 ∪ W2 ∪ W3) W4 := by
    rw [Finset.disjoint_left]; intro q h123 h4
    simp only [W1, W2, W3, W4, R3, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_erase, Finset.mem_Icc] at h123 h4
    subst h4
    rcases h123 with (h | ⟨_, _, h⟩) | ⟨y, ⟨_, _, hyhi⟩, h⟩
    · simp at h
    · simp at h
    · simp only [Prod.mk.injEq, neg_inj] at h; omega
  have hWcard : W.card = 6 * j + 5 := by
    change (W1 ∪ W2 ∪ W3 ∪ W4).card = 6 * j + 5
    rw [Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
      Finset.card_union_of_disjoint hd12, hcard1, hcard2, hcard3, hcard4]
    omega
  have hge : 6 * j + 5 ≤ projLineCount (S_K j) (1, 0, -K) := by
    rw [← hWcard]
    exact le_projLineCount_of_witness (S_K_proper j) hp W hW_sub hW_wit
  exact le_antisymm hle hge

/-- **Exact Tightness Euclidean Headline for `12j+11 family` (`j ≥ 2`)**: every point lies on at most
`6j + 5` spanned lines, and some point lies on **exact equality** `6j + 5`. -/
theorem class12j11_euclidean_tight {j : ℕ} (hj : 2 ≤ j) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 12 * j + 11 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 6 * j + 5) ∧
      (∃ a ∈ P, lineCountR2 P a = 6 * j + 5) := by
  have hK : 6 ≤ Kval j := by unfold Kval; omega
  have hp : (1, 0, -Kval j) ∈ S_K j :=
    mem_S_K_iff.mpr (Or.inl ⟨Kval j, mem_Jset_iff.mpr (by omega), rfl⟩)
  exact exists_euclidean_set_eq (S_K_proper j) (S_K_card hj) (S_K_nonCollinear hj)
    (S_K_lineCount_le hj) ⟨_, hp, le_of_eq (S_K_top_lineCount hj).symm⟩

/-- `X(11)`: the 11-point dual of the 5 sides + 5 diagonals of a regular pentagon + `ℓ_∞`,
encoded over `ℤ[φ]` (`φ² = φ + 1`), where every point spans `5` lines. -/
def x11Pts : List QPt :=
  let z : QInt := (0, 0)
  let o : QInt := (1, 0)
  let m : QInt := (-1, 0)
  let p : QInt := (0, 1)
  let ip : QInt := (-1, 1)
  let np1 : QInt := (-1, -1)
  [ (z, o, z), (o, m, z), (o, z, z), (o, ip, z),
    (o, z, m), (o, ip, m), (o, p, m), (o, p, np1),
    (z, o, m), (o, m, p), (z, z, o) ]

theorem cert_x11 : checkQSet 1 1 x11Pts 5 = true := by decide

/-- Closing `j = 0` (`n = 11`) of `12j+11 family`: explicit `11`-point Euclidean set with
every point on at most `5 = (11 - 1)/2` spanned lines. -/
theorem class12j11_j0_euclidean :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 11 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 5 :=
  exists_euclidean_of_checkQSet phi_sq phi_ker cert_x11

/-- `O25 \ 2`: `23` points of the octagon set `O25` (Grünbaum's `A(25, 5)` minus two ring
points), encoded over `ℤ[√2]` (`(√2)² = 2`), with every point on at most `10` spanned lines. -/
def o23Pts : List QPt :=
  let z : QInt := (0, 0)
  let o : QInt := (1, 0)
  let m : QInt := (-1, 0)
  let s : QInt := (0, 1)
  let ns : QInt := (0, -1)
  let s1 : QInt := (1, 1)
  let ns1 : QInt := (-1, -1)
  let s2 : QInt := (2, 1)
  let ns2 : QInt := (-2, -1)
  [ (z, z, o),
    (s, z, o), (ns, z, o), (z, s, o), (z, ns, o),
    (o, o, o), (o, m, o), (m, o, o), (m, m, o),
    (s2, z, o), (ns2, z, o), (z, s2, o), (z, ns2, o),
    (s1, s1, o), (s1, ns1, o),
    (o, z, z), (z, o, z), (o, o, z), (o, m, z),
    (o, s1, z), (o, ns1, z), (s1, o, z), (s1, m, z) ]

theorem cert_o23 : checkQSet 0 2 o23Pts 10 = true := by decide

/-- Closing `j = 1` (`n = 23`) of `12j+11 family`: explicit `23`-point Euclidean set with
every point on at most `10` (and hence `≤ 11 = (23 - 1)/2`) spanned lines. -/
theorem class12j11_j1_euclidean :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 23 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 10 :=
  exists_euclidean_of_checkQSet sqrt2_sq sqrt2_ker cert_o23

/-- **Complete All-`j` Theorem for `n = 12j + 11`**: for **every** `j : ℕ` (`j = 0, 1, 2, ...`),
there exists a non-collinear Euclidean set of `12j + 11` points with every point on at most
`6j + 5 = (n - 1) / 2` spanned lines. -/
theorem class12j11_all_j_euclidean (j : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 12 * j + 11 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 6 * j + 5 := by
  match j with
  | 0 => exact class12j11_j0_euclidean
  | 1 =>
    obtain ⟨P, hPc, hPnc, hPbd⟩ := class12j11_j1_euclidean
    exact ⟨P, hPc, hPnc, fun a ha => (hPbd a ha).trans (by omega)⟩
  | j + 2 => exact class12j11_euclidean (by omega)

/-! ### Section 3: Target B — Self-Contained All-`n ≥ 8` Mod-12 Dirac Counterexamples -/

/-- 4-direction square grid `Q(a, 0)` of `4a + 5` projective points (`a ≥ 1`):
`(1, 0, c)` and `(0, 1, c)` for `c ∈ [-a, a]`, plus `(1, 1, 0)`, `(1, -1, 0)`, `(0, 0, 1)`. -/
def sqGrid (a : ℕ) : Finset Pt :=
  (Finset.Icc (-(a : ℤ)) (a : ℤ)).image (fun c => (1, 0, c)) ∪
  (Finset.Icc (-(a : ℤ)) (a : ℤ)).image (fun c => (0, 1, c)) ∪
  {(1, 1, 0), (1, -1, 0), (0, 0, 1)}

lemma mem_sqGrid_iff {a : ℕ} {p : Pt} :
    p ∈ sqGrid a ↔
      (∃ c ∈ Finset.Icc (-(a : ℤ)) (a : ℤ), p = (1, 0, c)) ∨
      (∃ c ∈ Finset.Icc (-(a : ℤ)) (a : ℤ), p = (0, 1, c)) ∨
      p = (1, 1, 0) ∨ p = (1, -1, 0) ∨ p = (0, 0, 1) := by
  simp only [sqGrid, Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ((⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | rfl | rfl | rfl)
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl)
    · exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem sqGrid_card (a : ℕ) : (sqGrid a).card = 4 * a + 5 := by
  let A1 : Finset Pt := (Finset.Icc (-(a : ℤ)) (a : ℤ)).image (fun c => (1, 0, c))
  let A2 : Finset Pt := (Finset.Icc (-(a : ℤ)) (a : ℤ)).image (fun c => (0, 1, c))
  let A3 : Finset Pt := {(1, 1, 0), (1, -1, 0), (0, 0, 1)}
  have h1 : A1.card = 2 * a + 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simp at h; exact h), Int.card_Icc]; omega
  have h2 : A2.card = 2 * a + 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simp at h; exact h), Int.card_Icc]; omega
  have h3 : A3.card = 3 := by decide
  have hd12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro p h1' h2'
    simp only [A1, A2, Finset.mem_image] at h1' h2'
    rcases h1' with ⟨_, _, rfl⟩; rcases h2' with ⟨_, _, h⟩; simp at h
  have hd123 : Disjoint (A1 ∪ A2) A3 := by
    rw [Finset.disjoint_left]; intro p h12' h3'
    simp only [A1, A2, A3, Finset.mem_union, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton] at h12' h3'
    rcases h3' with rfl | rfl | rfl <;> rcases h12' with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp at h
  change (A1 ∪ A2 ∪ A3).card = 4 * a + 5
  rw [Finset.card_union_of_disjoint hd123, Finset.card_union_of_disjoint hd12, h1, h2, h3]
  omega

theorem sqGrid_proper (a : ℕ) : Proper (sqGrid a) := by
  constructor
  · intro p hp
    rcases mem_sqGrid_iff.mp hp with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl <;>
      simp [Nonzero]
  · intro p hp q hq hs
    rcases hs with ⟨u, v, hu, hv, hx, hy, hz⟩
    rcases mem_sqGrid_iff.mp hp with ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | rfl | rfl | rfl <;>
    rcases mem_sqGrid_iff.mp hq with ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | rfl | rfl | rfl <;>
    simp only at hx hy hz <;>
    first
    | rfl
    | (exfalso; omega)
    | (have huv : u = v := by omega
       subst huv
       have : u * (c₁ - c₂) = 0 := by linear_combination hz
       have hc : c₁ = c₂ := by have := (mul_eq_zero.mp this).resolve_left hu; omega
       subst hc; rfl)

theorem sqGrid_nonCollinear_erase_inf {a : ℕ} (ha : 1 ≤ a) :
    NonCollinear ((sqGrid a).erase (0, 0, 1)) := by
  have h1 : (1 : ℤ) ∈ Finset.Icc (-(a : ℤ)) (a : ℤ) := Finset.mem_Icc.mpr (by omega)
  refine ⟨(1, 0, 1), Finset.mem_erase.mpr ⟨by simp, mem_sqGrid_iff.mpr (Or.inl ⟨1, h1, rfl⟩)⟩,
          (0, 1, 1), Finset.mem_erase.mpr ⟨by simp, mem_sqGrid_iff.mpr (Or.inr (Or.inl ⟨1, h1, rfl⟩))⟩,
          (1, 1, 0), Finset.mem_erase.mpr ⟨by simp, mem_sqGrid_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩,
          by decide⟩

theorem sqGrid_lineCount_le {a : ℕ} (ha : 1 ≤ a) :
    ∀ p ∈ sqGrid a, projLineCount (sqGrid a) p ≤ 2 * a + 2 := by
  let L : Finset (Option ℤ) := insert none ((Finset.Icc (-(a : ℤ)) (a : ℤ)).image some)
  have hLcard : L.card = 2 * a + 2 := by
    have hnone : none ∉ (Finset.Icc (-(a : ℤ)) (a : ℤ)).image some := by simp
    rw [Finset.card_insert_of_notMem hnone,
      Finset.card_image_of_injective _ (fun _ _ h => Option.some.inj h), Int.card_Icc]
    omega
  intro p hp
  rcases mem_sqGrid_iff.mp hp with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl
  · -- p = (1, 0, c)
    rw [Finset.mem_Icc] at hc
    let lbl : Pt → Option ℤ := fun q =>
      if q.2.1 = 0 then none
      else if q = (1, 1, 0) then some (-c)
      else if q = (1, -1, 0) then some c
      else some q.2.2
    refine projLineCount_le_of_label (sqGrid_proper a) hp lbl L (by omega) ?_ ?_
    · intro q hq
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq) with
        ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | rfl | rfl | rfl
      · simp [lbl, L]
      · simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte,
          show ((0 : ℤ), (1 : ℤ), d) ≠ (1, 1, 0) by simp,
          show ((0 : ℤ), (1 : ℤ), d) ≠ (1, -1, 0) by simp]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd)
      · simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · simp only [lbl, show (-1 : ℤ) ≠ 0 by omega, ↓reduceIte,
          show ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) ≠ (1, 1, 0) by simp]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · simp [lbl, L]
    · intro q₁ hq₁ q₂ hq₂ heq
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₁) with
        ⟨d₁, _, rfl⟩ | ⟨d₁, _, rfl⟩ | rfl | rfl | rfl <;>
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₂) with
        ⟨d₂, _, rfl⟩ | ⟨d₂, _, rfl⟩ | rfl | rfl | rfl <;>
      (simp only [lbl] at heq; simp only [det]; (try simp at heq); try omega)
  · -- p = (0, 1, c)
    rw [Finset.mem_Icc] at hc
    let lbl : Pt → Option ℤ := fun q =>
      if q.1 = 0 then none
      else if q = (1, 1, 0) then some (-c)
      else if q = (1, -1, 0) then some c
      else some q.2.2
    refine projLineCount_le_of_label (sqGrid_proper a) hp lbl L (by omega) ?_ ?_
    · intro q hq
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq) with
        ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | rfl | rfl | rfl
      · simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte,
          show ((1 : ℤ), (0 : ℤ), d) ≠ (1, 1, 0) by simp,
          show ((1 : ℤ), (0 : ℤ), d) ≠ (1, -1, 0) by simp]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd)
      · simp [lbl, L]
      · simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte,
          show ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) ≠ (1, 1, 0) by simp]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · simp [lbl, L]
    · intro q₁ hq₁ q₂ hq₂ heq
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₁) with
        ⟨d₁, _, rfl⟩ | ⟨d₁, _, rfl⟩ | rfl | rfl | rfl <;>
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₂) with
        ⟨d₂, _, rfl⟩ | ⟨d₂, _, rfl⟩ | rfl | rfl | rfl <;>
      (simp only [lbl] at heq; simp only [det]; (try simp at heq); try omega)
  · -- p = (1, 1, 0)
    let lbl : Pt → Option ℤ := fun q =>
      if q = (0, 0, 1) then none
      else if q = (1, -1, 0) then some 0
      else if q.1 = 1 then some q.2.2
      else some (-q.2.2)
    refine projLineCount_le_of_label (sqGrid_proper a) hp lbl L (by omega) ?_ ?_
    · intro q hq
      have hne : q ≠ (1, 1, 0) := (Finset.mem_erase.mp hq).1
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq) with
        ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | rfl | rfl | rfl
      · simp only [lbl, show ((1 : ℤ), (0 : ℤ), d) ≠ (0, 0, 1) by simp,
          show ((1 : ℤ), (0 : ℤ), d) ≠ (1, -1, 0) by simp, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd)
      · rw [Finset.mem_Icc] at hd
        simp only [lbl, show ((0 : ℤ), (1 : ℤ), d) ≠ (0, 0, 1) by simp,
          show ((0 : ℤ), (1 : ℤ), d) ≠ (1, -1, 0) by simp,
          show (0 : ℤ) ≠ 1 by omega, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · exact absurd rfl hne
      · simp only [lbl, show ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) ≠ (0, 0, 1) by simp, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · simp [lbl, L]
    · intro q₁ hq₁ q₂ hq₂ heq
      have hne₁ : q₁ ≠ (1, 1, 0) := (Finset.mem_erase.mp hq₁).1
      have hne₂ : q₂ ≠ (1, 1, 0) := (Finset.mem_erase.mp hq₂).1
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₁) with
        ⟨d₁, _, rfl⟩ | ⟨d₁, _, rfl⟩ | rfl | rfl | rfl <;>
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₂) with
        ⟨d₂, _, rfl⟩ | ⟨d₂, _, rfl⟩ | rfl | rfl | rfl <;>
      (try exact absurd rfl hne₁) <;> (try exact absurd rfl hne₂) <;>
      (simp only [lbl] at heq; simp only [det]; (try simp at heq); try omega)
  · -- p = (1, -1, 0)
    let lbl : Pt → Option ℤ := fun q =>
      if q = (0, 0, 1) then none
      else if q = (1, 1, 0) then some 0
      else some q.2.2
    refine projLineCount_le_of_label (sqGrid_proper a) hp lbl L (by omega) ?_ ?_
    · intro q hq
      have hne : q ≠ (1, -1, 0) := (Finset.mem_erase.mp hq).1
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq) with
        ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | rfl | rfl | rfl
      · simp only [lbl, show ((1 : ℤ), (0 : ℤ), d) ≠ (0, 0, 1) by simp,
          show ((1 : ℤ), (0 : ℤ), d) ≠ (1, 1, 0) by simp, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd)
      · simp only [lbl, show ((0 : ℤ), (1 : ℤ), d) ≠ (0, 0, 1) by simp,
          show ((0 : ℤ), (1 : ℤ), d) ≠ (1, 1, 0) by simp, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hd)
      · simp only [lbl, show ((1 : ℤ), (1 : ℤ), (0 : ℤ)) ≠ (0, 0, 1) by simp, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))
      · exact absurd rfl hne
      · simp [lbl, L]
    · intro q₁ hq₁ q₂ hq₂ heq
      have hne₁ : q₁ ≠ (1, -1, 0) := (Finset.mem_erase.mp hq₁).1
      have hne₂ : q₂ ≠ (1, -1, 0) := (Finset.mem_erase.mp hq₂).1
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₁) with
        ⟨d₁, _, rfl⟩ | ⟨d₁, _, rfl⟩ | rfl | rfl | rfl <;>
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq₂) with
        ⟨d₂, _, rfl⟩ | ⟨d₂, _, rfl⟩ | rfl | rfl | rfl <;>
      (try exact absurd rfl hne₁) <;> (try exact absurd rfl hne₂) <;>
      (simp only [lbl] at heq; simp only [det]; (try simp at heq); try omega)
  · -- p = (0, 0, 1)
    let L4 : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (1, 1), (1, -1)}
    have h4 : L4.card = 4 := by decide
    refine projLineCount_le_of_label (sqGrid_proper a) hp (fun q => (q.1, q.2.1)) L4 (by omega) ?_ ?_
    · intro q hq
      have hne : q ≠ (0, 0, 1) := (Finset.mem_erase.mp hq).1
      rcases mem_sqGrid_iff.mp (Finset.mem_of_mem_erase hq) with
        ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl
      · simp [L4]
      · simp [L4]
      · simp [L4]
      · simp [L4]
      · exact absurd rfl hne
    · intro q₁ _ q₂ _ heq
      have ⟨h1, h2⟩ := Prod.mk.inj heq
      unfold det; rw [h1, h2]; ring

/-- All `n ≡ 1 (mod 4)` (`n ≥ 9`) and `n ≡ 0 (mod 4)` (`n ≥ 8`) via `sqGrid a`. -/
theorem sqGrid_mod4_euclidean {a : ℕ} (ha : 1 ≤ a) :
    (∃ P : Finset (ℝ × ℝ), P.card = 4 * a + 5 ∧ NonCollinearR2 P ∧
      ∀ x ∈ P, lineCountR2 P x ≤ 2 * a + 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 4 * a + 4 ∧ NonCollinearR2 P ∧
      ∀ x ∈ P, lineCountR2 P x ≤ 2 * a + 2) := by
  have hnc_erase := sqGrid_nonCollinear_erase_inf ha
  have hnc : NonCollinear (sqGrid a) := by
    rcases hnc_erase with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  have hinf : (0, 0, 1) ∈ sqGrid a :=
    mem_sqGrid_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  exact ⟨exists_euclidean_set_le (sqGrid_proper a) (sqGrid_card a) hnc (sqGrid_lineCount_le ha),
    exists_euclidean_erase_one (sqGrid_proper a) (sqGrid_card a) hinf hnc_erase
      (sqGrid_lineCount_le ha)⟩

/-! #### Felsner's Family `F_{2k}` (`n = 12k + 7`, `t ≤ 6k + 2`) and 4-Deletion Family (`n = 12k + 3`, `t ≤ 6k + 1`) -/

/-- Felsner's even-parameter projective point set `F_{2k}` (`n = 12k + 7`, deficit `3/2`). -/
def felsnerSet (k : ℕ) : Finset Pt :=
  let K : ℤ := 2 * (k : ℤ)
  (Finset.Icc (-K) K).image (fun c => (1, 0, -c)) ∪
  (Finset.Icc (-K) K).image (fun c => (0, 1, -c)) ∪
  (Finset.Icc (-K) K).image (fun c => (1, 1, -c)) ∪ Mpts

lemma mem_felsnerSet_iff {k : ℕ} {p : Pt} :
    p ∈ felsnerSet k ↔
      (∃ c ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)), p = (1, 0, -c)) ∨
      (∃ c ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)), p = (0, 1, -c)) ∨
      (∃ c ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)), p = (1, 1, -c)) ∨
      p = (1, -1, 0) ∨ p = (1, 2, 0) ∨ p = (2, 1, 0) ∨ p = (0, 0, 1) := by
  simp only [felsnerSet, Mpts, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (((⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩) | rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl)
    · exact Or.inl (Or.inl (Or.inl ⟨c, hc, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨c, hc, rfl⟩))
    · exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem felsnerSet_card (k : ℕ) : (felsnerSet k).card = 12 * k + 7 := by
  let K : ℤ := 2 * (k : ℤ)
  let A1 : Finset Pt := (Finset.Icc (-K) K).image (fun c => (1, 0, -c))
  let A2 : Finset Pt := (Finset.Icc (-K) K).image (fun c => (0, 1, -c))
  let A3 : Finset Pt := (Finset.Icc (-K) K).image (fun c => (1, 1, -c))
  have h1 : A1.card = 4 * k + 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simp at h; exact h), Int.card_Icc]; omega
  have h2 : A2.card = 4 * k + 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simp at h; exact h), Int.card_Icc]; omega
  have h3 : A3.card = 4 * k + 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simp at h; exact h), Int.card_Icc]; omega
  have hM : Mpts.card = 4 := by decide
  have hd12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro p h1' h2'
    simp only [A1, A2, Finset.mem_image] at h1' h2'
    rcases h1' with ⟨_, _, rfl⟩; rcases h2' with ⟨_, _, h⟩; simp at h
  have hd123 : Disjoint (A1 ∪ A2) A3 := by
    rw [Finset.disjoint_left]; intro p h12' h3'
    simp only [A1, A2, A3, Finset.mem_union, Finset.mem_image] at h12' h3'
    rcases h3' with ⟨_, _, rfl⟩; rcases h12' with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp at h
  have hd1234 : Disjoint (A1 ∪ A2 ∪ A3) Mpts := by
    rw [Finset.disjoint_left]; intro p h123' hM'
    simp only [A1, A2, A3, Mpts, Finset.mem_union, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton] at h123' hM'
    rcases hM' with rfl | rfl | rfl | rfl <;>
      rcases h123' with (⟨_, _, h⟩ | ⟨_, _, h⟩) | ⟨_, _, h⟩ <;> simp at h
  change (A1 ∪ A2 ∪ A3 ∪ Mpts).card = 12 * k + 7
  rw [Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
    Finset.card_union_of_disjoint hd12, h1, h2, h3, hM]
  omega

theorem felsnerSet_proper (k : ℕ) : Proper (felsnerSet k) := by
  constructor
  · intro p hp
    rcases mem_felsnerSet_iff.mp hp with
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl | rfl <;> simp [Nonzero]
  · intro p hp q hq hs
    rcases hs with ⟨u, v, hu, hv, hx, hy, hz⟩
    rcases mem_felsnerSet_iff.mp hp with
      ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    rcases mem_felsnerSet_iff.mp hq with
      ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    simp only at hx hy hz <;>
    first
    | rfl
    | (exfalso; omega)
    | (have huv : u = v := by omega
       subst huv
       have : u * (c₂ - c₁) = 0 := by linear_combination hz
       have hc : c₁ = c₂ := by have := (mul_eq_zero.mp this).resolve_left hu; omega
       subst hc; rfl)

/-- Order-3 projective symmetry of `felsnerSet k`: `(x, y, z) ↦ ±(-y, x - y, z)`. -/
def rotF (p : Pt) : Pt :=
  if p.1 = 0 ∧ p.2.1 = 1 then (1, 1, -p.2.2)
  else if p.1 = 1 ∧ p.2.1 = 1 then (1, 0, -p.2.2)
  else if p = (1, 2, 0) then (2, 1, 0)
  else if p = (2, 1, 0) then (1, -1, 0)
  else (-p.2.1, p.1 - p.2.1, p.2.2)

/-- Inverse of `rotF` on `felsnerSet k`. -/
def rotFInv (p : Pt) : Pt := rotF (rotF p)

/-- Sign flip `z ↦ -z` keeping `(0, 0, 1)` fixed. -/
def flipZF (p : Pt) : Pt := if p = (0, 0, 1) then (0, 0, 1) else negZ p

private lemma det_rotF_aux (a b c : Pt) :
    det (-a.2.1, a.1 - a.2.1, a.2.2) (-b.2.1, b.1 - b.2.1, b.2.2) (-c.2.1, c.1 - c.2.1, c.2.2) =
      det a b c := by
  unfold det; ring

private lemma rotF_signed (p : Pt) :
    rotF p = (-p.2.1, p.1 - p.2.1, p.2.2) ∨
    rotF p = (-(-p.2.1), -(p.1 - p.2.1), -p.2.2) := by
  rcases p with ⟨x, y, z⟩
  by_cases h1 : x = 0 ∧ y = 1
  · rcases h1 with ⟨rfl, rfl⟩; right; simp [rotF]
  · by_cases h2 : x = 1 ∧ y = 1
    · rcases h2 with ⟨rfl, rfl⟩; right; simp [rotF]
    · by_cases h3 : (x, y, z) = (1, 2, 0)
      · rcases Prod.mk.inj h3 with ⟨rfl, h3'⟩
        rcases Prod.mk.inj h3' with ⟨rfl, rfl⟩
        right; simp [rotF]
      · by_cases h4 : (x, y, z) = (2, 1, 0)
        · rcases Prod.mk.inj h4 with ⟨rfl, h4'⟩
          rcases Prod.mk.inj h4' with ⟨rfl, rfl⟩
          right; simp [rotF]
        · left; simp [rotF, h1, h2, h3, h4]

private lemma det_scale_eq_zero {f g : Pt → Pt}
    (hg : ∀ a b c, det (g a) (g b) (g c) = 0 ↔ det a b c = 0)
    (hs : ∀ p, f p = g p ∨ f p = (-(g p).1, -(g p).2.1, -(g p).2.2)) :
    ∀ a b c, det (f a) (f b) (f c) = 0 ↔ det a b c = 0 := by
  intro a b c
  have h1 : ∀ u v w : Pt, det (-u.1, -u.2.1, -u.2.2) v w = -det u v w := by
    intro u v w; unfold det; ring
  have h2 : ∀ u v w : Pt, det u (-v.1, -v.2.1, -v.2.2) w = -det u v w := by
    intro u v w; unfold det; ring
  have h3 : ∀ u v w : Pt, det u v (-w.1, -w.2.1, -w.2.2) = -det u v w := by
    intro u v w; unfold det; ring
  rcases hs a with ha | ha <;> rcases hs b with hb | hb <;> rcases hs c with hc | hc <;>
    rw [ha, hb, hc] <;>
    simp only [h1, h2, h3, neg_eq_zero, hg]

lemma projLineCount_rotF {k : ℕ} {p : Pt} (hp : p ∈ felsnerSet k) :
    projLineCount (felsnerSet k) (rotF p) = projLineCount (felsnerSet k) p := by
  have hmem : ∀ q ∈ felsnerSet k, rotF q ∈ felsnerSet k := by
    intro q hq
    rcases mem_felsnerSet_iff.mp hq with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨c, hc, by simp [rotF]⟩))
    · rw [Finset.mem_Icc] at hc
      exact mem_felsnerSet_iff.mpr
        (Or.inr (Or.inr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), by simp [rotF]⟩)))
    · rw [Finset.mem_Icc] at hc
      exact mem_felsnerSet_iff.mpr
        (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), by simp [rotF]⟩)
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [rotF]))))))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [rotF])))))))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [rotF])))))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [rotF])))))))
  have h3 : ∀ q ∈ felsnerSet k, rotF (rotF (rotF q)) = q := by
    intro q hq
    rcases mem_felsnerSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl <;> simp [rotF]
  refine projLineCount_eq_of_det_equiv (felsnerSet_proper k) hp rotF rotFInv
    hmem (fun q hq => hmem _ (hmem _ hq)) (fun q hq => h3 q hq) (fun q hq => h3 q hq) ?_
  exact det_scale_eq_zero (fun a b c => by rw [det_rotF_aux]) rotF_signed

lemma projLineCount_flipZF {k : ℕ} {p : Pt} (hp : p ∈ felsnerSet k) :
    projLineCount (felsnerSet k) (flipZF p) = projLineCount (felsnerSet k) p := by
  have hmem : ∀ q ∈ felsnerSet k, flipZF q ∈ felsnerSet k := by
    intro q hq
    rcases mem_felsnerSet_iff.mp hq with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
    · rw [Finset.mem_Icc] at hc
      exact mem_felsnerSet_iff.mpr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), by simp [flipZF, negZ]⟩)
    · rw [Finset.mem_Icc] at hc
      exact mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), by simp [flipZF, negZ]⟩))
    · rw [Finset.mem_Icc] at hc
      exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), by simp [flipZF, negZ]⟩)))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [flipZF, negZ])))))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [flipZF, negZ]))))))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [flipZF, negZ])))))))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [flipZF])))))))
  have hinvol : ∀ q ∈ felsnerSet k, flipZF (flipZF q) = q := by
    intro q hq
    rcases mem_felsnerSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl <;> simp [flipZF, negZ]
  refine projLineCount_eq_of_det_equiv (felsnerSet_proper k) hp flipZF flipZF
    hmem hmem hinvol hinvol ?_
  refine det_scale_eq_zero (g := negZ) (fun a b c => by rw [det_negZ, neg_eq_zero]) (fun q => ?_)
  by_cases h : q = (0, 0, 1)
  · subst h; right; simp [flipZF, negZ]
  · left; simp [flipZF, h]

/-- Precise line count for `(1, 0, -c)` (`0 ≤ c ≤ 2k`) in `felsnerSet k`:
at most `6k + 2` for all `c`, and at most `6k + 1` whenever `c ≤ 2k - 2`. -/
lemma felsnerSet_lineCount_X {k : ℕ} (hk : 1 ≤ k) {c : ℤ}
    (hc0 : 0 ≤ c) (hcK : c ≤ 2 * (k : ℤ)) :
    projLineCount (felsnerSet k) (1, 0, -c) ≤
      if c ≤ 2 * (k : ℤ) - 2 then 6 * k + 1 else 6 * k + 2 := by
  set K : ℤ := 2 * (k : ℤ)
  have hp : (1, 0, -c) ∈ felsnerSet k :=
    mem_felsnerSet_iff.mpr (Or.inl ⟨c, Finset.mem_Icc.mpr (by omega), rfl⟩)
  -- Label q ∈ X.erase (1, 0, -c) by Option ℤ:
  --   none for q.2.1 = 0 (parallel x-lines and (0,0,1))
  --   some (2 * y) where y is the exact crossing height on x = c:
  --     (0, 1, -d) -> 2*d, (1, 1, -s) -> 2*(s - c),
  --     (1, -1, 0) -> 2*c, (2, 1, 0) -> -4*c, (1, 2, 0) -> -c.
  let lbl : Pt → Option ℤ := fun q =>
    if q.2.1 = 0 then none
    else if q = (1, 2, 0) then some (-c)
    else if q = (1, -1, 0) then some (2 * c)
    else if q = (2, 1, 0) then some (-4 * c)
    else if q.1 = 0 then some (-2 * q.2.2)
    else some (-2 * q.2.2 - 2 * c)
  let evens : Finset ℤ := (Finset.Icc (-K - c) K).image (fun y => 2 * y)
  let L : Finset (Option ℤ) :=
    if c % 2 = 0 then insert none (evens.image some)
    else insert none (insert (some (-c)) (evens.image some))
  have hLcard : L.card ≤ if c ≤ K - 2 then 6 * k + 1 else 6 * k + 2 := by
    have hev : evens.card = (2 * K + c + 1).toNat := by
      rw [Finset.card_image_of_injective _ (fun x y h => by omega), Int.card_Icc]; omega
    have himg : (evens.image some).card = evens.card :=
      Finset.card_image_of_injective _ (fun _ _ h => Option.some.inj h)
    by_cases hpar : c % 2 = 0
    · simp only [L, hpar, ↓reduceIte]
      have h1 : (insert (none : Option ℤ) (evens.image some)).card ≤ (evens.image some).card + 1 :=
        Finset.card_insert_le _ _
      split_ifs <;> omega
    · simp only [L, hpar, ↓reduceIte]
      have h1 : (insert (none : Option ℤ) (insert (some (-c)) (evens.image some))).card ≤
          (insert (some (-c)) (evens.image some)).card + 1 := Finset.card_insert_le _ _
      have h2 : (insert (some (-c)) (evens.image some)).card ≤ (evens.image some).card + 1 :=
        Finset.card_insert_le _ _
      -- Note: when c is odd and c ≤ K = 2k, actually c ≤ K - 1!
      split_ifs <;> omega
  have hmem_ev : ∀ y : ℤ, -K - c ≤ y → y ≤ K → some (2 * y) ∈ L := by
    intro y hlo hhi
    have hy : 2 * y ∈ evens := Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hlo, hhi⟩)
    by_cases hpar : c % 2 = 0
    · simp only [L, hpar, ↓reduceIte]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy)
    · simp only [L, hpar, ↓reduceIte]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  refine projLineCount_le_of_label (felsnerSet_proper k) hp lbl L hLcard ?_ ?_
  · intro q hq
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq) with
      ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | ⟨s, hs, rfl⟩ | rfl | rfl | rfl | rfl
    · simp only [lbl, ↓reduceIte]
      by_cases hpar : c % 2 = 0 <;> simp [L, hpar]
    · rw [Finset.mem_Icc] at hd
      simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte,
        show ((0 : ℤ), (1 : ℤ), -d) ≠ (1, 2, 0) by simp,
        show ((0 : ℤ), (1 : ℤ), -d) ≠ (1, -1, 0) by simp,
        show ((0 : ℤ), (1 : ℤ), -d) ≠ (2, 1, 0) by simp]
      rw [show -2 * -d = 2 * d by ring]
      exact hmem_ev d (by omega) (by omega)
    · rw [Finset.mem_Icc] at hs
      simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte,
        show ((1 : ℤ), (1 : ℤ), -s) ≠ (1, 2, 0) by simp,
        show ((1 : ℤ), (1 : ℤ), -s) ≠ (1, -1, 0) by simp,
        show ((1 : ℤ), (1 : ℤ), -s) ≠ (2, 1, 0) by simp]
      rw [show -2 * -s - 2 * c = 2 * (s - c) by ring]
      exact hmem_ev (s - c) (by omega) (by omega)
    · simp only [lbl, show (-1 : ℤ) ≠ 0 by omega, ↓reduceIte,
        show ((1 : ℤ), (-1 : ℤ), (0 : ℤ)) ≠ (1, 2, 0) by simp]
      exact hmem_ev c (by omega) (by omega)
    · simp only [lbl, show (2 : ℤ) ≠ 0 by omega, ↓reduceIte]
      by_cases hpar : c % 2 = 0
      · have hhalf : -c = 2 * (-(c / 2)) := by omega
        rw [hhalf]
        exact hmem_ev (-(c / 2)) (by omega) (by omega)
      · simp only [L, hpar, ↓reduceIte]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · simp only [lbl, show (1 : ℤ) ≠ 0 by omega, ↓reduceIte,
        show ((2 : ℤ), (1 : ℤ), (0 : ℤ)) ≠ (1, 2, 0) by simp,
        show ((2 : ℤ), (1 : ℤ), (0 : ℤ)) ≠ (1, -1, 0) by simp]
      rw [show -4 * c = 2 * (-2 * c) by ring]
      exact hmem_ev (-2 * c) (by omega) (by omega)
    · simp only [lbl, ↓reduceIte]
      by_cases hpar : c % 2 = 0 <;> simp [L, hpar]
  · intro q₁ hq₁ q₂ hq₂ heq
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq₁) with
      ⟨d₁, _, rfl⟩ | ⟨d₁, _, rfl⟩ | ⟨s₁, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq₂) with
      ⟨d₂, _, rfl⟩ | ⟨d₂, _, rfl⟩ | ⟨s₂, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    (simp only [lbl] at heq; simp only [det]; (try simp at heq); try omega)

lemma felsnerSet_lineCount_M1 {k : ℕ} (hk : 1 ≤ k) :
    projLineCount (felsnerSet k) (1, -1, 0) ≤ 6 * k + 2 := by
  set K : ℤ := 2 * (k : ℤ)
  have hp : (1, -1, 0) ∈ felsnerSet k :=
    mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  let lbl : Pt → Option ℤ := fun q =>
    if q = (0, 0, 1) then none
    else if q = (1, 2, 0) ∨ q = (2, 1, 0) then some 0
    else if q.1 = 1 ∧ q.2.1 = 1 then some (-q.2.2)
    else some (-2 * q.2.2)
  let evens : Finset ℤ := (Finset.Icc (-K) K).image (fun c => 2 * c)
  let odds : Finset ℤ := (Finset.Icc (-(k : ℤ)) ((k : ℤ) - 1)).image (fun m => 2 * m + 1)
  let L : Finset (Option ℤ) := insert none ((evens ∪ odds).image some)
  have hLcard : L.card ≤ 6 * k + 2 := by
    have hev : evens.card = 4 * k + 1 := by
      rw [Finset.card_image_of_injective _ (fun x y h => by omega), Int.card_Icc]; omega
    have hodd : odds.card = 2 * k := by
      rw [Finset.card_image_of_injective _ (fun x y h => by omega), Int.card_Icc]; omega
    calc L.card ≤ ((evens ∪ odds).image some).card + 1 := Finset.card_insert_le _ _
      _ ≤ (evens ∪ odds).card + 1 := by gcongr; exact Finset.card_image_le
      _ ≤ (evens.card + odds.card) + 1 := by gcongr; exact Finset.card_union_le _ _
      _ = 6 * k + 2 := by omega
  refine projLineCount_le_of_label (felsnerSet_proper k) hp lbl L hLcard ?_ ?_
  · intro q hq
    have hne : q ≠ (1, -1, 0) := (Finset.mem_erase.mp hq).1
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq) with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨s, hs, rfl⟩ | rfl | rfl | rfl | rfl
    · simp only [lbl, show ((1 : ℤ), (0 : ℤ), -c) ≠ (0, 0, 1) by simp,
        show ¬(((1 : ℤ), (0 : ℤ), -c) = (1, 2, 0) ∨ ((1 : ℤ), (0 : ℤ), -c) = (2, 1, 0)) by simp,
        ↓reduceIte]
      rw [show -2 * -c = 2 * c by ring]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ hc)))
    · simp only [lbl, show ((0 : ℤ), (1 : ℤ), -c) ≠ (0, 0, 1) by simp,
        show ¬(((0 : ℤ), (1 : ℤ), -c) = (1, 2, 0) ∨ ((0 : ℤ), (1 : ℤ), -c) = (2, 1, 0)) by simp,
        ↓reduceIte]
      rw [show -2 * -c = 2 * c by ring]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ hc)))
    · rw [Finset.mem_Icc] at hs
      simp only [lbl, show ((1 : ℤ), (1 : ℤ), -s) ≠ (0, 0, 1) by simp,
        show ¬(((1 : ℤ), (1 : ℤ), -s) = (1, 2, 0) ∨ ((1 : ℤ), (1 : ℤ), -s) = (2, 1, 0)) by simp,
        and_self, ↓reduceIte, neg_neg]
      by_cases hpar : s % 2 = 0
      · have hs' : s = 2 * (s / 2) := by omega
        rw [hs']
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))))
      · have hs' : s = 2 * ((s - 1) / 2) + 1 := by omega
        rw [hs']
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (by omega)))))
    · exact absurd rfl hne
    · simp only [lbl, show ((1 : ℤ), (2 : ℤ), (0 : ℤ)) ≠ (0, 0, 1) by simp, true_or, ↓reduceIte]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr (by omega), by ring⟩)))
    · simp only [lbl, show ((2 : ℤ), (1 : ℤ), (0 : ℤ)) ≠ (0, 0, 1) by simp, or_true, ↓reduceIte]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr (by omega), by ring⟩)))
    · simp [lbl, L]
  · intro q₁ hq₁ q₂ hq₂ heq
    have hne₁ : q₁ ≠ (1, -1, 0) := (Finset.mem_erase.mp hq₁).1
    have hne₂ : q₂ ≠ (1, -1, 0) := (Finset.mem_erase.mp hq₂).1
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq₁) with
      ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨s₁, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq₂) with
      ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨s₂, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    (try exact absurd rfl hne₁) <;> (try exact absurd rfl hne₂) <;>
    (simp only [lbl] at heq; simp only [det]; (try simp at heq); try omega)

lemma felsnerSet_lineCount_inf {k : ℕ} (_hk : 1 ≤ k) :
    projLineCount (felsnerSet k) (0, 0, 1) ≤ 6 := by
  have hp : (0, 0, 1) ∈ felsnerSet k :=
    mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  let L6 : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1)}
  refine projLineCount_le_of_label (felsnerSet_proper k) hp (fun q => (q.1, q.2.1)) L6
    (by decide) ?_ ?_
  · intro q hq
    have hne : q ≠ (0, 0, 1) := (Finset.mem_erase.mp hq).1
    rcases mem_felsnerSet_iff.mp (Finset.mem_of_mem_erase hq) with
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl | rfl
    · simp [L6]
    · simp [L6]
    · simp [L6]
    · simp [L6]
    · simp [L6]
    · simp [L6]
    · exact absurd rfl hne
  · intro q₁ _ q₂ _ heq
    have ⟨h1, h2⟩ := Prod.mk.inj heq
    unfold det; rw [h1, h2]; ring

/-- **Felsner's Theorem (`F_{2k}`, `k ≥ 1`)**: every point of `felsnerSet k` lies on at most
`6k + 2 = (n - 3) / 2` lines (deficit `3/2`). -/
theorem felsnerSet_lineCount_le {k : ℕ} (hk : 1 ≤ k) :
    ∀ p ∈ felsnerSet k, projLineCount (felsnerSet k) p ≤ 6 * k + 2 := by
  have hXall : ∀ c ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)),
      projLineCount (felsnerSet k) (1, 0, -c) ≤ 6 * k + 2 := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    by_cases h0 : 0 ≤ c
    · have h := felsnerSet_lineCount_X hk h0 hc.2
      split_ifs at h <;> omega
    · have hp : (1, 0, -c) ∈ felsnerSet k :=
        mem_felsnerSet_iff.mpr (Or.inl ⟨c, Finset.mem_Icc.mpr hc, rfl⟩)
      have hsym : flipZF (1, 0, -c) = (1, 0, -(-c)) := by simp [flipZF, negZ]
      rw [← projLineCount_flipZF hp, hsym]
      have h := felsnerSet_lineCount_X hk (c := -c) (by omega) (by omega)
      split_ifs at h <;> omega
  intro p hp
  rcases mem_felsnerSet_iff.mp hp with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · exact hXall c hc
  · have hpre : (1, 0, -c) ∈ felsnerSet k := mem_felsnerSet_iff.mpr (Or.inl ⟨c, hc, rfl⟩)
    have hrot : rotF (1, 0, -c) = (0, 1, -c) := by simp [rotF]
    rw [← hrot, projLineCount_rotF hpre]
    exact hXall c hc
  · rw [Finset.mem_Icc] at hc
    have hpre : (1, 0, -(-c)) ∈ felsnerSet k :=
      mem_felsnerSet_iff.mpr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), rfl⟩)
    have hrot : rotF (rotF (1, 0, -(-c))) = (1, 1, -c) := by simp [rotF]
    rw [← hrot, projLineCount_rotF (by
      have : rotF (1, 0, -(-c)) = (0, 1, -(-c)) := by simp [rotF]
      rw [this]; exact mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), rfl⟩))),
      projLineCount_rotF hpre]
    exact hXall (-c) (Finset.mem_Icc.mpr (by omega))
  · exact felsnerSet_lineCount_M1 hk
  · have hpre : (1, -1, 0) ∈ felsnerSet k :=
      mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hrot : rotF (1, -1, 0) = (1, 2, 0) := by simp [rotF]
    rw [← hrot, projLineCount_rotF hpre]
    exact felsnerSet_lineCount_M1 hk
  · have hpre : (1, -1, 0) ∈ felsnerSet k :=
      mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hrot : rotF (rotF (1, -1, 0)) = (2, 1, 0) := by simp [rotF]
    rw [← hrot, projLineCount_rotF (by
      have : rotF (1, -1, 0) = (1, 2, 0) := by simp [rotF]
      rw [this]; exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
      projLineCount_rotF hpre]
    exact felsnerSet_lineCount_M1 hk
  · exact (felsnerSet_lineCount_inf hk).trans (by omega)

/-- Euclidean Felsner theorem (`n = 12k + 7` at `≤ 6k + 2` and `n = 12k + 6` at `≤ 6k + 2`, `k ≥ 1`). -/
theorem felsner_mod12_euclidean {k : ℕ} (hk : 1 ≤ k) :
    (∃ P : Finset (ℝ × ℝ), P.card = 12 * k + 7 ∧ NonCollinearR2 P ∧
      ∀ x ∈ P, lineCountR2 P x ≤ 6 * k + 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 12 * k + 6 ∧ NonCollinearR2 P ∧
      ∀ x ∈ P, lineCountR2 P x ≤ 6 * k + 2) := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)) := Finset.mem_Icc.mpr (by omega)
  have h1 : (1 : ℤ) ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)) := Finset.mem_Icc.mpr (by omega)
  have hinf : (0, 0, 1) ∈ felsnerSet k :=
    mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have hnc_erase : NonCollinear ((felsnerSet k).erase (0, 0, 1)) :=
    ⟨(1, 0, 0), Finset.mem_erase.mpr ⟨by simp, mem_felsnerSet_iff.mpr (Or.inl ⟨0, h0, by simp⟩)⟩,
     (0, 1, 0), Finset.mem_erase.mpr ⟨by simp, mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨0, h0, by simp⟩))⟩,
     (1, 0, -1), Finset.mem_erase.mpr ⟨by simp, mem_felsnerSet_iff.mpr (Or.inl ⟨1, h1, rfl⟩)⟩,
     by decide⟩
  have hnc : NonCollinear (felsnerSet k) := by
    rcases hnc_erase with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  exact ⟨exists_euclidean_set_le (felsnerSet_proper k) (felsnerSet_card k) hnc
      (felsnerSet_lineCount_le hk),
    exists_euclidean_erase_one (felsnerSet_proper k) (felsnerSet_card k) hinf hnc_erase
      (felsnerSet_lineCount_le hk)⟩

/-- The four deleted points `D_4 = {(1, 0, -3), (0, 1, -3), (1, 1, -3), (0, 1, 3)}` for `12k + 3`. -/
def felsnerD4 : Finset Pt := {(1, 0, -3), (0, 1, -3), (1, 1, -3), (0, 1, 3)}

/-- 4-deletion Felsner set `F_{2k} \ D_4` of size `12k + 3` (`k ≥ 3`), every point on `≤ 6k + 1` lines. -/
def felsnerDel4 (k : ℕ) : Finset Pt := felsnerSet k \ felsnerD4

private lemma felsner_ord_drop {k : ℕ} (hk : 3 ≤ k) {p q : Pt}
    (hp : p ∈ felsnerSet k) (hqD : q ∈ felsnerD4) (hqF : q ∈ felsnerSet k) (hqp : q ≠ p)
    (hord : IsOrdinaryLine (felsnerSet k) p q) :
    projLineCount (felsnerDel4 k) p ≤ 6 * k + 1 := by
  have hsub := projLineCount_sdiff_le_sub (D := felsnerD4) (W := {q})
    (felsnerSet_proper k) hp (Finset.singleton_subset_iff.mpr hqD)
    (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨hqp, hqF⟩))
    (fun r hr => by rw [Finset.mem_singleton.mp hr]; exact hord)
  have hbd := felsnerSet_lineCount_le (by omega : 1 ≤ k) p hp
  simp only [Finset.card_singleton] at hsub
  unfold felsnerDel4
  omega

private lemma felsner_isOrd_of_pieces {k : ℕ} {p q : Pt}
    (hX : ∀ c : ℤ, -(2 * (k : ℤ)) ≤ c → c ≤ 2 * (k : ℤ) → det p q (1, 0, -c) = 0 →
      (1, 0, -c) = p ∨ (1, 0, -c) = q)
    (hY : ∀ c : ℤ, -(2 * (k : ℤ)) ≤ c → c ≤ 2 * (k : ℤ) → det p q (0, 1, -c) = 0 →
      (0, 1, -c) = p ∨ (0, 1, -c) = q)
    (hZ : ∀ c : ℤ, -(2 * (k : ℤ)) ≤ c → c ≤ 2 * (k : ℤ) → det p q (1, 1, -c) = 0 →
      (1, 1, -c) = p ∨ (1, 1, -c) = q)
    (hM1 : det p q (1, -1, 0) = 0 → (1, -1, 0) = p ∨ (1, -1, 0) = q)
    (hM2 : det p q (1, 2, 0) = 0 → (1, 2, 0) = p ∨ (1, 2, 0) = q)
    (hM3 : det p q (2, 1, 0) = 0 → (2, 1, 0) = p ∨ (2, 1, 0) = q)
    (hInf : det p q (0, 0, 1) = 0 → (0, 0, 1) = p ∨ (0, 0, 1) = q) :
    IsOrdinaryLine (felsnerSet k) p q := by
  intro r hr hdet
  rcases mem_felsnerSet_iff.mp hr with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · rw [Finset.mem_Icc] at hc; exact hX c hc.1 hc.2 hdet
  · rw [Finset.mem_Icc] at hc; exact hY c hc.1 hc.2 hdet
  · rw [Finset.mem_Icc] at hc; exact hZ c hc.1 hc.2 hdet
  · exact hM1 hdet
  · exact hM2 hdet
  · exact hM3 hdet
  · exact hInf hdet

theorem felsnerDel4_mod12_euclidean {k : ℕ} (hk : 3 ≤ k) :
    (∃ P : Finset (ℝ × ℝ), P.card = 12 * k + 3 ∧ NonCollinearR2 P ∧
      ∀ x ∈ P, lineCountR2 P x ≤ 6 * k + 1) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 12 * k + 2 ∧ NonCollinearR2 P ∧
      ∀ x ∈ P, lineCountR2 P x ≤ 6 * k + 1) := by
  have hD4_sub : felsnerD4 ⊆ felsnerSet k := by
    intro q hq
    simp only [felsnerD4, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact mem_felsnerSet_iff.mpr (Or.inl ⟨3, Finset.mem_Icc.mpr (by omega), rfl⟩)
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨3, Finset.mem_Icc.mpr (by omega), rfl⟩))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨3, Finset.mem_Icc.mpr (by omega), rfl⟩)))
    · exact mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨-3, Finset.mem_Icc.mpr (by omega), by simp⟩))
  have hD4_card : felsnerD4.card = 4 := by decide
  have hcard : (felsnerDel4 k).card = 12 * k + 3 := by
    unfold felsnerDel4
    rw [Finset.card_sdiff_of_subset hD4_sub, felsnerSet_card k, hD4_card]
    omega
  have hprop : Proper (felsnerDel4 k) := proper_subset (felsnerSet_proper k) Finset.sdiff_subset
  have hbound : ∀ p ∈ felsnerDel4 k, projLineCount (felsnerDel4 k) p ≤ 6 * k + 1 := by
    have hX_inner : ∀ c : ℤ, -(2 * (k : ℤ)) + 2 ≤ c → c ≤ 2 * (k : ℤ) - 2 →
        projLineCount (felsnerSet k) (1, 0, -c) ≤ 6 * k + 1 := by
      intro c hlo hhi
      by_cases h0 : 0 ≤ c
      · have h := felsnerSet_lineCount_X (by omega : 1 ≤ k) h0 (by omega)
        simpa [hhi] using h
      · have hp : (1, 0, -c) ∈ felsnerSet k :=
          mem_felsnerSet_iff.mpr (Or.inl ⟨c, Finset.mem_Icc.mpr (by omega), rfl⟩)
        have hsym : flipZF (1, 0, -c) = (1, 0, -(-c)) := by simp [flipZF, negZ]
        rw [← projLineCount_flipZF hp, hsym]
        have h := felsnerSet_lineCount_X (by omega : 1 ≤ k) (c := -c) (by omega) (by omega)
        have hhi' : -c ≤ 2 * (k : ℤ) - 2 := by omega
        simpa [hhi'] using h
    have hq1 : (1, 0, -3) ∈ felsnerD4 := by simp [felsnerD4]
    have hq2 : (0, 1, -3) ∈ felsnerD4 := by simp [felsnerD4]
    have hq3 : (1, 1, -3) ∈ felsnerD4 := by simp [felsnerD4]
    have hq4 : (0, 1, 3) ∈ felsnerD4 := by simp [felsnerD4]
    have hord_Xneg : ∀ c : ℤ, c = -(2 * (k : ℤ)) ∨ c = 1 - 2 * (k : ℤ) →
        IsOrdinaryLine (felsnerSet k) (1, 0, -c) (1, 1, -3) := fun c hc =>
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d hlo hhi hd => by simp only [det] at hd; exfalso; omega)
        (fun d hlo hhi hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_Xpos : ∀ c : ℤ, c = 2 * (k : ℤ) ∨ c = 2 * (k : ℤ) - 1 →
        IsOrdinaryLine (felsnerSet k) (1, 0, -c) (0, 1, -3) := fun c hc =>
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d hlo hhi hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_Yneg : ∀ c : ℤ, c = -(2 * (k : ℤ)) ∨ c = 1 - 2 * (k : ℤ) →
        IsOrdinaryLine (felsnerSet k) (0, 1, -c) (1, 1, -3) := fun c hc =>
      felsner_isOrd_of_pieces
        (fun d hlo hhi hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_Ypos : ∀ c : ℤ, c = 2 * (k : ℤ) ∨ c = 2 * (k : ℤ) - 1 →
        IsOrdinaryLine (felsnerSet k) (0, 1, -c) (1, 0, -3) := fun c hc =>
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d _ _ hd => by simp only [det] at hd; left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d hlo hhi hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_Zneg : ∀ c : ℤ, c = -(2 * (k : ℤ)) ∨ c = 1 - 2 * (k : ℤ) →
        IsOrdinaryLine (felsnerSet k) (1, 1, -c) (1, 0, -3) := fun c hc =>
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d hlo hhi hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_Zpos : ∀ c : ℤ, c = 2 * (k : ℤ) ∨ c = 2 * (k : ℤ) - 1 →
        IsOrdinaryLine (felsnerSet k) (1, 1, -c) (0, 1, 3) := fun c hc =>
      felsner_isOrd_of_pieces
        (fun d hlo hhi hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d _ _ hd => by simp only [det] at hd; left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_M1 : IsOrdinaryLine (felsnerSet k) (1, -1, 0) (1, 1, -3) :=
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun _ => Or.inl rfl)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_M2 : IsOrdinaryLine (felsnerSet k) (1, 2, 0) (1, 0, -3) :=
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d _ _ hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun _ => Or.inl rfl)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    have hord_M3 : IsOrdinaryLine (felsnerSet k) (2, 1, 0) (0, 1, -3) :=
      felsner_isOrd_of_pieces
        (fun d _ _ hd => by simp only [det] at hd; exfalso; omega)
        (fun d _ _ hd => by simp only [det] at hd; right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
        (fun d _ _ hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun hd => by simp only [det] at hd; exfalso; omega)
        (fun _ => Or.inl rfl)
        (fun hd => by simp only [det] at hd; exfalso; omega)
    intro p hp
    have hpF : p ∈ felsnerSet k := (Finset.mem_sdiff.mp hp).1
    rcases mem_felsnerSet_iff.mp hpF with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
    · rw [Finset.mem_Icc] at hc
      by_cases hneg : c = -(2 * (k : ℤ)) ∨ c = 1 - 2 * (k : ℤ)
      · exact felsner_ord_drop hk hpF hq3 (hD4_sub hq3) (by simp) (hord_Xneg c hneg)
      · by_cases hpos : c = 2 * (k : ℤ) ∨ c = 2 * (k : ℤ) - 1
        · exact felsner_ord_drop hk hpF hq2 (hD4_sub hq2) (by simp) (hord_Xpos c hpos)
        · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hX_inner c (by omega) (by omega))
    · rw [Finset.mem_Icc] at hc
      by_cases hneg : c = -(2 * (k : ℤ)) ∨ c = 1 - 2 * (k : ℤ)
      · exact felsner_ord_drop hk hpF hq3 (hD4_sub hq3) (by simp) (hord_Yneg c hneg)
      · by_cases hpos : c = 2 * (k : ℤ) ∨ c = 2 * (k : ℤ) - 1
        · exact felsner_ord_drop hk hpF hq1 (hD4_sub hq1) (by simp) (hord_Ypos c hpos)
        · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
          have hpre : (1, 0, -c) ∈ felsnerSet k :=
            mem_felsnerSet_iff.mpr (Or.inl ⟨c, Finset.mem_Icc.mpr hc, rfl⟩)
          have hrot : rotF (1, 0, -c) = (0, 1, -c) := by simp [rotF]
          rw [← hrot, projLineCount_rotF hpre]
          exact hX_inner c (by omega) (by omega)
    · rw [Finset.mem_Icc] at hc
      by_cases hneg : c = -(2 * (k : ℤ)) ∨ c = 1 - 2 * (k : ℤ)
      · exact felsner_ord_drop hk hpF hq1 (hD4_sub hq1) (by simp) (hord_Zneg c hneg)
      · by_cases hpos : c = 2 * (k : ℤ) ∨ c = 2 * (k : ℤ) - 1
        · exact felsner_ord_drop hk hpF hq4 (hD4_sub hq4) (by simp) (hord_Zpos c hpos)
        · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
          have hpre : (1, 0, -(-c)) ∈ felsnerSet k :=
            mem_felsnerSet_iff.mpr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), rfl⟩)
          have hrot : rotF (rotF (1, 0, -(-c))) = (1, 1, -c) := by simp [rotF]
          rw [← hrot, projLineCount_rotF (by
            have : rotF (1, 0, -(-c)) = (0, 1, -(-c)) := by simp [rotF]
            rw [this]; exact mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨-c, Finset.mem_Icc.mpr (by omega), rfl⟩))),
            projLineCount_rotF hpre]
          exact hX_inner (-c) (by omega) (by omega)
    · exact felsner_ord_drop hk hpF hq3 (hD4_sub hq3) (by simp) hord_M1
    · exact felsner_ord_drop hk hpF hq1 (hD4_sub hq1) (by simp) hord_M2
    · exact felsner_ord_drop hk hpF hq2 (hD4_sub hq2) (by simp) hord_M3
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans
        ((felsnerSet_lineCount_inf (by omega : 1 ≤ k)).trans (by omega))
  have hinf : (0, 0, 1) ∈ felsnerDel4 k :=
    Finset.mem_sdiff.mpr ⟨mem_felsnerSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))),
      by simp [felsnerD4]⟩
  have hnc_erase : NonCollinear ((felsnerDel4 k).erase (0, 0, 1)) := by
    have h0 : (0 : ℤ) ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)) := Finset.mem_Icc.mpr (by omega)
    have h1 : (1 : ℤ) ∈ Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)) := Finset.mem_Icc.mpr (by omega)
    refine ⟨(1, 0, 0), Finset.mem_erase.mpr ⟨by simp,
        Finset.mem_sdiff.mpr ⟨mem_felsnerSet_iff.mpr (Or.inl ⟨0, h0, by simp⟩), by simp [felsnerD4]⟩⟩,
      (0, 1, 0), Finset.mem_erase.mpr ⟨by simp,
        Finset.mem_sdiff.mpr ⟨mem_felsnerSet_iff.mpr (Or.inr (Or.inl ⟨0, h0, by simp⟩)), by simp [felsnerD4]⟩⟩,
      (1, 0, -1), Finset.mem_erase.mpr ⟨by simp,
        Finset.mem_sdiff.mpr ⟨mem_felsnerSet_iff.mpr (Or.inl ⟨1, h1, rfl⟩), by simp [felsnerD4]⟩⟩,
      by decide⟩
  have hnc : NonCollinear (felsnerDel4 k) := by
    rcases hnc_erase with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  exact ⟨exists_euclidean_set_le hprop hcard hnc hbound,
    exists_euclidean_erase_one hprop hcard hinf hnc_erase hbound⟩

/-- Deleting `(0, 0, 1)` from `12j+11 family`'s `S_K j` (`j ≥ 2`) covers all `n = 12j + 10` (`n ≥ 34`). -/
theorem class12j11_erase_one_euclidean {j : ℕ} (hj : 2 ≤ j) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 12 * j + 10 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 6 * j + 5 := by
  have hK : 6 ≤ Kval j := by unfold Kval; omega
  have h0J : (0 : ℤ) ∈ Jset (Kval j) := mem_Jset_iff.mpr (by omega)
  have h2J : (2 : ℤ) ∈ Jset (Kval j) := mem_Jset_iff.mpr (by omega)
  have hinf : (0, 0, 1) ∈ S_K j :=
    mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have hnc_erase : NonCollinear ((S_K j).erase (0, 0, 1)) :=
    ⟨(1, 0, 0), Finset.mem_erase.mpr ⟨by simp, mem_S_K_iff.mpr (Or.inl ⟨0, h0J, by simp⟩)⟩,
     (0, 1, 0), Finset.mem_erase.mpr ⟨by simp, mem_S_K_iff.mpr (Or.inr (Or.inl ⟨0, h0J, by simp⟩))⟩,
     (1, 0, -2), Finset.mem_erase.mpr ⟨by simp, mem_S_K_iff.mpr (Or.inl ⟨2, h2J, rfl⟩)⟩,
     by decide⟩
  exact exists_euclidean_erase_one (S_K_proper j) (S_K_card hj) hinf hnc_erase (S_K_lineCount_le hj)

/-! #### Finite Small Witnesses Below `n = 38` (`n ∈ {10, 14, 15, 22, 26, 27}`) -/

/-- `A(15, 1) = H_3` icosahedral reflection arrangement (`n = 15, t = 6`) over `ℤ[φ]`. -/
def h3Pts : List QPt :=
  let z : QInt := (0, 0)
  let o : QInt := (1, 0)
  let p : QInt := (0, 1)
  let np : QInt := (0, -1)
  let ip : QInt := (-1, 1)
  let nip : QInt := (1, -1)
  [ (o, z, z), (z, o, z), (z, z, o),
    (o, p, ip), (ip, o, p), (p, ip, o),
    (o, p, nip), (nip, o, p), (p, nip, o),
    (o, np, ip), (ip, o, np), (np, ip, o),
    (o, np, nip), (nip, o, np), (np, nip, o) ]

def h3Del1Pts : List QPt := h3Pts.drop 1

/-- Pure-integer triangular grid without medians (`n = 10, t = 5` at `K = 1`; `n = 22, t = 11` at `K = 3`). -/
def triNoMedPts (K : ℤ) : List QPt :=
  ofIntPt (0, 0, 1) ::
  ((List.range (2 * K.toNat + 1)).flatMap fun i =>
    let c : ℤ := (i : ℤ) - K
    [ofIntPt (1, 0, -c), ofIntPt (0, 1, -c), ofIntPt (1, 1, -c)])

/-- Pure-integer 4-deletion of `F_4` (`n = 27, t = 13`) and 5-deletion (`n = 26, t ≤ 13`). -/
def f4Del4Pts : List QPt :=
  let drop : List Pt := [(1, 1, -3), (1, 0, -3), (0, 1, -1), (2, 1, 0)]
  let raw : List Pt :=
    [(0, 0, 1), (1, -1, 0), (1, 2, 0), (2, 1, 0)] ++
    ((List.range 9).flatMap fun i =>
      let c : ℤ := (i : ℤ) - 4
      [(1, 0, -c), (0, 1, -c), (1, 1, -c)])
  (raw.filter (fun p => !drop.contains p)).map ofIntPt

def f4Del5Pts : List QPt := f4Del4Pts.drop 1

theorem cert_h3 : checkQSet 1 1 h3Pts 6 = true := by decide
theorem cert_h3_del1 : checkQSet 1 1 h3Del1Pts 6 = true := by decide
theorem cert_n10 : checkQSet 0 2 (triNoMedPts 1) 5 = true := by decide
theorem cert_n22 : checkQSet 0 2 (triNoMedPts 3) 11 = true := by decide
theorem cert_n27 : checkQSet 0 2 f4Del4Pts 13 = true := by decide
theorem cert_n26 : checkQSet 0 2 f4Del5Pts 13 = true := by decide

/-- **Self-Contained All-`n ≥ 8` Mod-12 Theorem (Target B)**: for **every** integer `n ≥ 8`
across all 12 residue classes mod 12, there exists a non-collinear Euclidean set `P` of `n`
points such that every point lies on at most `⌊n / 2⌋ = n / 2` spanned lines. -/
theorem dirac_counterexample_all_ge_8 (n : ℕ) (hn : 8 ≤ n) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ n / 2 := by
  have hmod : n % 12 < 12 := Nat.mod_lt n (by omega)
  let q := n / 12
  have hnq : n = 12 * q + n % 12 := by omega
  have hcase : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨
      n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 = 6 ∨ n % 12 = 7 ∨
      n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11 := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h
  · -- n = 12q (q ≥ 1), square grid a = 3q - 1
    have hq1 : 1 ≤ q := by omega
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (sqGrid_mod4_euclidean (a := 3 * q - 1) (by omega)).2
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 1 (q ≥ 1), square grid a = 3q - 1
    have hq1 : 1 ≤ q := by omega
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (sqGrid_mod4_euclidean (a := 3 * q - 1) (by omega)).1
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 2: q = 1 (n=14), q = 2 (n=26), q ≥ 3 (felsnerDel4)
    rcases (show q = 1 ∨ q = 2 ∨ 3 ≤ q by omega) with hq1 | hq2 | hq3
    · have hn14 : n = 14 := by omega
      subst hn14
      obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_of_checkQSet phi_sq phi_ker cert_h3_del1
      exact ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
    · have hn26 : n = 26 := by omega
      subst hn26
      obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_of_checkQSet sqrt2_sq sqrt2_ker cert_n26
      exact ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
    · obtain ⟨P, hPc, hPnc, hPbd⟩ := (felsnerDel4_mod12_euclidean hq3).2
      exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 3: q = 1 (n=15), q = 2 (n=27), q ≥ 3 (felsnerDel4)
    rcases (show q = 1 ∨ q = 2 ∨ 3 ≤ q by omega) with hq1 | hq2 | hq3
    · have hn15 : n = 15 := by omega
      subst hn15
      obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_of_checkQSet phi_sq phi_ker cert_h3
      exact ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
    · have hn27 : n = 27 := by omega
      subst hn27
      obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_of_checkQSet sqrt2_sq sqrt2_ker cert_n27
      exact ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
    · obtain ⟨P, hPc, hPnc, hPbd⟩ := (felsnerDel4_mod12_euclidean hq3).1
      exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 4 (q ≥ 1), square grid a = 3q
    have hq1 : 1 ≤ q := by omega
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (sqGrid_mod4_euclidean (a := 3 * q) (by omega)).2
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 5 (q ≥ 1), square grid a = 3q
    have hq1 : 1 ≤ q := by omega
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (sqGrid_mod4_euclidean (a := 3 * q) (by omega)).1
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 6 (q ≥ 1), Felsner F_{2q} minus 1
    have hq1 : 1 ≤ q := by omega
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (felsner_mod12_euclidean hq1).2
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 7 (q ≥ 1), Felsner F_{2q}
    have hq1 : 1 ≤ q := by omega
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (felsner_mod12_euclidean hq1).1
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 8 (q ≥ 0), square grid a = 3q + 1
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (sqGrid_mod4_euclidean (a := 3 * q + 1) (by omega)).2
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 9 (q ≥ 0), square grid a = 3q + 1
    obtain ⟨P, hPc, hPnc, hPbd⟩ := (sqGrid_mod4_euclidean (a := 3 * q + 1) (by omega)).1
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 10: q = 0 (n=10), q = 1 (n=22), q ≥ 2 (S_K erase 1)
    rcases (show q = 0 ∨ q = 1 ∨ 2 ≤ q by omega) with hq0 | hq1 | hq2
    · have hn10 : n = 10 := by omega
      subst hn10
      obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_of_checkQSet sqrt2_sq sqrt2_ker cert_n10
      exact ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
    · have hn22 : n = 22 := by omega
      subst hn22
      obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_of_checkQSet sqrt2_sq sqrt2_ker cert_n22
      exact ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
    · obtain ⟨P, hPc, hPnc, hPbd⟩ := class12j11_erase_one_euclidean hq2
      exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩
  · -- n = 12q + 11 (q ≥ 0), complete all-j 12j+11 family!
    obtain ⟨P, hPc, hPnc, hPbd⟩ := class12j11_all_j_euclidean q
    exact ⟨P, by omega, hPnc, fun x hx => (hPbd x hx).trans (by omega)⟩

/-- Odd-`n` corollary: for every odd `n ≥ 9`, every point lies on at most `(n - 1) / 2` lines. -/
theorem dirac_counterexample_all_odd_ge_9 (n : ℕ) (hn : 9 ≤ n) (hodd : Odd n) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ (n - 1) / 2 := by
  obtain ⟨P, hPc, hPnc, hPbd⟩ := dirac_counterexample_all_ge_8 n (by omega)
  rcases hodd with ⟨m, rfl⟩
  exact ⟨P, hPc, hPnc, fun a ha => (hPbd a ha).trans (by omega)⟩

/-! ### Section 4: Target C — 12-Class Mod-60 Refutation of Grünbaum's 2010 Conjecture -/

/-- The 8 second-to-outermost knight points `(1, ±2, ±m2), (2, ±1, ±m2)`. -/
def knightD8 (m2 : ℤ) : Finset Pt :=
  {(1, 2, m2), (1, 2, -m2), (1, -2, m2), (1, -2, -m2),
   (2, 1, m2), (2, 1, -m2), (2, -1, m2), (2, -1, -m2)}

/-- The 4 second-to-outermost knight points in directions `(1, ±2)`. -/
def knightD4 (m2 : ℤ) : Finset Pt :=
  {(1, 2, m2), (1, 2, -m2), (1, -2, m2), (1, -2, -m2)}

/-- `Family C` Family C (`s ≥ 1`): `familyB s \ D_8`, size `60s + 61 = 12(5s+5) + 1`, exact `t = 30s + 28`. -/
def familyC (s : ℕ) : Finset Pt := familyB s \ knightD8 (5 * (s : ℤ) + 3)

/-- `Family E4` Family E4 (`s ≥ 1`): `familyB s \ D_4`, size `60s + 65`, `t ≤ 30s + 31`. -/
def familyBE4 (s : ℕ) : Finset Pt := familyB s \ knightD4 (5 * (s : ℤ) + 3)

/-- New 8-deletion Family `A \ D_8` (`s ≥ 2`): size `60s + 45`, `t ≤ 30s + 21`. -/
def familyAD8 (s : ℕ) : Finset Pt := familyA s \ knightD8 (5 * (s : ℤ) + 1)

/-- New 4-deletion Family `A \ D_4` (`s ≥ 2`): size `60s + 49`, `t ≤ 30s + 23`. -/
def familyAD4 (s : ℕ) : Finset Pt := familyA s \ knightD4 (5 * (s : ℤ) + 1)

lemma card_knightD8 {m2 : ℤ} (hm : 0 < m2) : (knightD8 m2).card = 8 := by
  unfold knightD8
  rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_singleton]

lemma card_knightD4 {m2 : ℤ} (hm : 0 < m2) : (knightD4 m2).card = 4 := by
  unfold knightD4
  rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_singleton]

lemma knightD8_subset_knightSet {a e b m : ℕ} (hm : 2 ≤ m) :
    knightD8 ((m : ℤ) - 2) ⊆ knightSet a e b m := by
  have hp : ((m : ℤ) - 2) ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
  have hn : -((m : ℤ) - 2) ∈ parityRange m := neg_mem_parityRange hp
  intro q hq
  simp only [knightD8, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hp, rfl⟩)))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hn, rfl⟩)))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hp, rfl⟩))))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hn, rfl⟩))))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hp, rfl⟩)))))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hn, rfl⟩)))))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hp, rfl⟩))))))))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hn, rfl⟩))))))))

lemma knightD4_subset_knightD8 (m2 : ℤ) : knightD4 m2 ⊆ knightD8 m2 := by
  intro q hq
  simp only [knightD4, knightD8, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  tauto

theorem familyC_card {s : ℕ} (hs : 1 ≤ s) : (familyC s).card = 60 * s + 61 := by
  unfold familyC
  have hsub : knightD8 (5 * (s : ℤ) + 3) ⊆ familyB s := by
    have heq : (5 * (s : ℤ) + 3) = (((5 * s + 5 : ℕ) : ℤ) - 2) := by push_cast; ring
    rw [heq]; exact knightD8_subset_knightSet (by omega)
  rw [Finset.card_sdiff_of_subset hsub, familyB_card s, card_knightD8 (by omega)]
  omega

theorem familyBE4_card {s : ℕ} (hs : 1 ≤ s) : (familyBE4 s).card = 60 * s + 65 := by
  unfold familyBE4
  have hsub : knightD4 (5 * (s : ℤ) + 3) ⊆ familyB s := by
    have heq : (5 * (s : ℤ) + 3) = (((5 * s + 5 : ℕ) : ℤ) - 2) := by push_cast; ring
    rw [heq]; exact (knightD4_subset_knightD8 _).trans (knightD8_subset_knightSet (by omega))
  rw [Finset.card_sdiff_of_subset hsub, familyB_card s, card_knightD4 (by omega)]
  omega

theorem familyAD8_card {s : ℕ} (hs : 2 ≤ s) : (familyAD8 s).card = 60 * s + 45 := by
  unfold familyAD8
  have hsub : knightD8 (5 * (s : ℤ) + 1) ⊆ familyA s := by
    have heq : (5 * (s : ℤ) + 1) = (((5 * s + 3 : ℕ) : ℤ) - 2) := by push_cast; ring
    rw [heq]; exact knightD8_subset_knightSet (by omega)
  rw [Finset.card_sdiff_of_subset hsub, familyA_card s, card_knightD8 (by omega)]
  omega

theorem familyAD4_card {s : ℕ} (hs : 2 ≤ s) : (familyAD4 s).card = 60 * s + 49 := by
  unfold familyAD4
  have hsub : knightD4 (5 * (s : ℤ) + 1) ⊆ familyA s := by
    have heq : (5 * (s : ℤ) + 1) = (((5 * s + 3 : ℕ) : ℤ) - 2) := by push_cast; ring
    rw [heq]; exact (knightD4_subset_knightD8 _).trans (knightD8_subset_knightSet (by omega))
  rw [Finset.card_sdiff_of_subset hsub, familyA_card s, card_knightD4 (by omega)]
  omega

/-! #### Symmetry Invariance of `knightSet \ D` -/

private lemma projLineCount_sdiff_invol {X D : Finset Pt} (hX : Proper X)
    {f : Pt → Pt}
    (hfX : ∀ q ∈ X, f q ∈ X)
    (hfD : ∀ q ∈ D, f q ∈ D)
    (hinvol : ∀ q ∈ X, f (f q) = q)
    (hdet : ∀ a b c, det (f a) (f b) (f c) = 0 ↔ det a b c = 0)
    {p : Pt} (hp : p ∈ X \ D) :
    projLineCount (X \ D) (f p) = projLineCount (X \ D) p := by
  have hmem : ∀ q ∈ X \ D, f q ∈ X \ D := by
    intro q hq
    rcases Finset.mem_sdiff.mp hq with ⟨hqX, hqnD⟩
    refine Finset.mem_sdiff.mpr ⟨hfX q hqX, fun hfqD => hqnD ?_⟩
    rw [← hinvol q hqX]
    exact hfD _ hfqD
  exact projLineCount_eq_of_det_equiv (proper_subset hX Finset.sdiff_subset) hp f f
    hmem hmem (fun q hq => hinvol q (Finset.mem_sdiff.mp hq).1)
    (fun q hq => hinvol q (Finset.mem_sdiff.mp hq).1) hdet

private lemma knightSet_symZ_props (a e b m : ℕ) :
    (∀ q ∈ knightSet a e b m, symZ q ∈ knightSet a e b m) ∧
    (∀ q ∈ knightSet a e b m, symZ (symZ q) = q) ∧
    (∀ x y z, det (symZ x) (symZ y) (symZ z) = 0 ↔ det x y z = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
    · have hnc : -c ∈ parityRange a ∪ parityRange e := by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_left _ (neg_mem_parityRange h)
        · exact Finset.mem_union_right _ (neg_mem_parityRange h)
      exact mem_knightSet_iff.mpr (Or.inl ⟨-c, hnc, by simp [symZ, negZ]⟩)
    · have hnc : -c ∈ parityRange a ∪ parityRange e := by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_left _ (neg_mem_parityRange h)
        · exact Finset.mem_union_right _ (neg_mem_parityRange h)
      exact mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨-c, hnc, by simp [symZ, negZ]⟩))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symZ, negZ]⟩)))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symZ, negZ]⟩))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symZ, negZ]⟩)))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symZ, negZ]⟩))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symZ, negZ]⟩)))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symZ, negZ]⟩))))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [symZ])))))))))
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ |
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl <;>
    simp [symZ, negZ]
  · refine det_scale_eq_zero (g := negZ) (fun x y z => by rw [det_negZ, neg_eq_zero]) (fun q => ?_)
    by_cases h : q = (0, 0, 1)
    · subst h; right; simp [symZ, negZ]
    · left; simp [symZ, h]

private lemma knightSet_symY_props (a e b m : ℕ) :
    (∀ q ∈ knightSet a e b m, symY q ∈ knightSet a e b m) ∧
    (∀ q ∈ knightSet a e b m, symY (symY q) = q) ∧
    (∀ x y z, det (symY x) (symY y) (symY z) = 0 ↔ det x y z = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
    · exact mem_knightSet_iff.mpr (Or.inl ⟨c, hc, by simp [symY, negY]⟩)
    · have hnc : -c ∈ parityRange a ∪ parityRange e := by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_left _ (neg_mem_parityRange h)
        · exact Finset.mem_union_right _ (neg_mem_parityRange h)
      exact mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨-c, hnc, by simp [symY]⟩))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symY, negY]⟩))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symY, negY]⟩)))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symY, negY]⟩))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symY, negY]⟩)))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symY, negY]⟩))))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symY, negY]⟩)))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [symY, negY])))))))))
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ |
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl <;>
    simp [symY, negY]
  · refine det_scale_eq_zero (g := negY) (fun x y z => by rw [det_negY, neg_eq_zero]) (fun q => ?_)
    by_cases h : q.1 = 0 ∧ q.2.1 = 1
    · right; rcases q with ⟨x, y, z⟩; simp only at h; rcases h with ⟨rfl, rfl⟩; simp [symY, negY]
    · left; simp [symY, h]

private lemma knightSet_symXY_props (a e b m : ℕ) :
    (∀ q ∈ knightSet a e b m, symXY q ∈ knightSet a e b m) ∧
    (∀ q ∈ knightSet a e b m, symXY (symXY q) = q) ∧
    (∀ x y z, det (symXY x) (symXY y) (symXY z) = 0 ↔ det x y z = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨c, hc, by simp [symXY, swapXY]⟩))
    · exact mem_knightSet_iff.mpr (Or.inl ⟨c, hc, by simp [symXY, swapXY]⟩)
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symXY, swapXY]⟩)))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symXY]⟩))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symXY, swapXY]⟩)))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symXY]⟩))))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [symXY, swapXY]⟩)))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨-c, neg_mem_parityRange hc, by simp [symXY]⟩))))))
    · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [symXY, swapXY])))))))))
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ |
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl <;>
    simp [symXY, swapXY]
  · refine det_scale_eq_zero (g := swapXY) (fun x y z => by rw [det_swapXY, neg_eq_zero]) (fun q => ?_)
    rcases q with ⟨x, y, z⟩
    by_cases h1 : x = 1 ∧ y = -1
    · right; rcases h1 with ⟨rfl, rfl⟩; simp [symXY, swapXY]
    · by_cases h2 : x = 1 ∧ y = -2
      · right; rcases h2 with ⟨rfl, rfl⟩; simp [symXY, swapXY]
      · by_cases h3 : x = 2 ∧ y = -1
        · right; rcases h3 with ⟨rfl, rfl⟩; simp [symXY, swapXY]
        · left; simp [symXY, h1, h2, h3]

private lemma knightD8_symZ {m2 : ℤ} : ∀ q ∈ knightD8 m2, symZ q ∈ knightD8 m2 := by
  intro q hq
  simp only [knightD8, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [symZ, negZ]

private lemma knightD8_symY {m2 : ℤ} : ∀ q ∈ knightD8 m2, symY q ∈ knightD8 m2 := by
  intro q hq
  simp only [knightD8, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [symY, negY]

private lemma knightD8_symXY {m2 : ℤ} : ∀ q ∈ knightD8 m2, symXY q ∈ knightD8 m2 := by
  intro q hq
  simp only [knightD8, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [symXY, swapXY]

private lemma knightD4_symZ {m2 : ℤ} : ∀ q ∈ knightD4 m2, symZ q ∈ knightD4 m2 := by
  intro q hq
  simp only [knightD4, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl <;> simp [symZ, negZ]

private lemma knightD4_symY {m2 : ℤ} : ∀ q ∈ knightD4 m2, symY q ∈ knightD4 m2 := by
  intro q hq
  simp only [knightD4, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl <;> simp [symY, negY]

/-! #### Shifted Interior `HullCert` Certificates for Family B (`s ≥ 1`) and Family A (`s ≥ 2`) -/

def branchB_evPencils : List Pencil := knightPencils 18 27 6 8 16 24 10 15 1 0 1
def branchA_evPencils : List Pencil := knightPencils 18 25 6 8 16 22 10 13 1 0 1
def branchA_oddPencils : List Pencil := knightPencils 18 34 6 11 16 30 10 18 0 1 0

private lemma cert_N2_of_6chunks' {ps : List Pencil} {rho0 m1 m0 N1 N0 : ℕ}
    (hhdr : certifyHeader 2 60 ps rho0 m1 m0 120 12 = true)
    (h0 : checkC0Range 120 (ps.map (Pencil.toAff 2 60)) m1 m0 120 12 N1 N0 ((m1 * 12) / 120) rho0 0 10 = true)
    (h1 : checkC0Range 120 (ps.map (Pencil.toAff 2 60)) m1 m0 120 12 N1 N0 ((m1 * 12) / 120) rho0 10 10 = true)
    (h2 : checkC0Range 120 (ps.map (Pencil.toAff 2 60)) m1 m0 120 12 N1 N0 ((m1 * 12) / 120) rho0 20 10 = true)
    (h3 : checkC0Range 120 (ps.map (Pencil.toAff 2 60)) m1 m0 120 12 N1 N0 ((m1 * 12) / 120) rho0 30 10 = true)
    (h4 : checkC0Range 120 (ps.map (Pencil.toAff 2 60)) m1 m0 120 12 N1 N0 ((m1 * 12) / 120) rho0 40 10 = true)
    (h5 : checkC0Range 120 (ps.map (Pencil.toAff 2 60)) m1 m0 120 12 N1 N0 ((m1 * 12) / 120) rho0 50 10 = true) :
    certifyTarget 2 60 ps rho0 m1 m0 120 12 N1 N0 = true := by
  refine certifyTarget_of_header_and_range hhdr ?_
  have h01 := checkC0Range_append h0 h1
  have h02 := checkC0Range_append h01 h2
  have h03 := checkC0Range_append h02 h3
  have h04 := checkC0Range_append h03 h4
  exact checkC0Range_append h04 h5

-- Family B odd `s = 2t + 1` (`branch3Pencils`): interior ≤ 30s + 28 = 1 + 60t + 57
theorem cert_Bodd_Xa_in : certifyTarget 0 2 (nonParallel 0 branch3Pencils) 0 18 16 4 2 60 57 = true := by decide
theorem cert_Bodd_Xe_in : certifyTarget 0 2 (nonParallel 0 branch3Pencils) 1 6 3 4 2 60 57 = true := by decide
theorem cert_Bodd_Xe_top : certifyTarget 0 2 (nonParallel 0 branch3Pencils) 1 6 5 4 2 60 59 = true := by decide
theorem cert_Bodd_S_in : certifyTarget 1 6 (nonParallel 1 branch3Pencils) 0 16 14 12 3 60 57 = true := by decide
private theorem cert_Bodd_N2_in_h : certifyHeader 2 60 (nonParallel 2 branch3Pencils) 0 10 4 120 12 = true := by decide
private theorem cert_Bodd_N2_in_0 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 4 120 12 60 57 1 0 0 10 = true := by decide
private theorem cert_Bodd_N2_in_1 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 4 120 12 60 57 1 0 10 10 = true := by decide
private theorem cert_Bodd_N2_in_2 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 4 120 12 60 57 1 0 20 10 = true := by decide
private theorem cert_Bodd_N2_in_3 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 4 120 12 60 57 1 0 30 10 = true := by decide
private theorem cert_Bodd_N2_in_4 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 4 120 12 60 57 1 0 40 10 = true := by decide
private theorem cert_Bodd_N2_in_5 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 4 120 12 60 57 1 0 50 10 = true := by decide
theorem cert_Bodd_N2_in : certifyTarget 2 60 (nonParallel 2 branch3Pencils) 0 10 4 120 12 60 57 = true :=
  cert_N2_of_6chunks' cert_Bodd_N2_in_h cert_Bodd_N2_in_0 cert_Bodd_N2_in_1 cert_Bodd_N2_in_2 cert_Bodd_N2_in_3 cert_Bodd_N2_in_4 cert_Bodd_N2_in_5

private theorem cert_Bodd_N2_m4_h : certifyHeader 2 60 (nonParallel 2 branch3Pencils) 0 10 6 120 12 = true := by decide
private theorem cert_Bodd_N2_m4_0 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 6 120 12 60 58 1 0 0 10 = true := by decide
private theorem cert_Bodd_N2_m4_1 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 6 120 12 60 58 1 0 10 10 = true := by decide
private theorem cert_Bodd_N2_m4_2 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 6 120 12 60 58 1 0 20 10 = true := by decide
private theorem cert_Bodd_N2_m4_3 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 6 120 12 60 58 1 0 30 10 = true := by decide
private theorem cert_Bodd_N2_m4_4 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 6 120 12 60 58 1 0 40 10 = true := by decide
private theorem cert_Bodd_N2_m4_5 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 6 120 12 60 58 1 0 50 10 = true := by decide
theorem cert_Bodd_N2_m4 : certifyTarget 2 60 (nonParallel 2 branch3Pencils) 0 10 6 120 12 60 58 = true :=
  cert_N2_of_6chunks' cert_Bodd_N2_m4_h cert_Bodd_N2_m4_0 cert_Bodd_N2_m4_1 cert_Bodd_N2_m4_2 cert_Bodd_N2_m4_3 cert_Bodd_N2_m4_4 cert_Bodd_N2_m4_5

-- Family B even `s = 2t + 2` (`branchB_evPencils`): interior ≤ 30s + 28 = 1 + 60t + 87
theorem cert_Bev_Xa_in : certifyTarget 0 2 (nonParallel 0 branchB_evPencils) 1 18 25 4 2 60 87 = true := by decide
theorem cert_Bev_Xe_in : certifyTarget 0 2 (nonParallel 0 branchB_evPencils) 0 6 6 4 2 60 87 = true := by decide
theorem cert_Bev_Xe_top : certifyTarget 0 2 (nonParallel 0 branchB_evPencils) 0 6 8 4 2 60 89 = true := by decide
theorem cert_Bev_S_in : certifyTarget 1 6 (nonParallel 1 branchB_evPencils) 0 16 22 12 3 60 87 = true := by decide
private theorem cert_Bev_N2_in_h : certifyHeader 2 60 (nonParallel 2 branchB_evPencils) 1 10 9 120 12 = true := by decide
private theorem cert_Bev_N2_in_0 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 87 1 1 0 10 = true := by decide
private theorem cert_Bev_N2_in_1 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 87 1 1 10 10 = true := by decide
private theorem cert_Bev_N2_in_2 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 87 1 1 20 10 = true := by decide
private theorem cert_Bev_N2_in_3 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 87 1 1 30 10 = true := by decide
private theorem cert_Bev_N2_in_4 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 87 1 1 40 10 = true := by decide
private theorem cert_Bev_N2_in_5 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 87 1 1 50 10 = true := by decide
theorem cert_Bev_N2_in : certifyTarget 2 60 (nonParallel 2 branchB_evPencils) 1 10 9 120 12 60 87 = true :=
  cert_N2_of_6chunks' cert_Bev_N2_in_h cert_Bev_N2_in_0 cert_Bev_N2_in_1 cert_Bev_N2_in_2 cert_Bev_N2_in_3 cert_Bev_N2_in_4 cert_Bev_N2_in_5

private theorem cert_Bev_N2_m4_h : certifyHeader 2 60 (nonParallel 2 branchB_evPencils) 1 10 11 120 12 = true := by decide
private theorem cert_Bev_N2_m4_0 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 11 120 12 60 88 1 1 0 10 = true := by decide
private theorem cert_Bev_N2_m4_1 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 11 120 12 60 88 1 1 10 10 = true := by decide
private theorem cert_Bev_N2_m4_2 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 11 120 12 60 88 1 1 20 10 = true := by decide
private theorem cert_Bev_N2_m4_3 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 11 120 12 60 88 1 1 30 10 = true := by decide
private theorem cert_Bev_N2_m4_4 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 11 120 12 60 88 1 1 40 10 = true := by decide
private theorem cert_Bev_N2_m4_5 : checkC0Range 120 ((nonParallel 2 branchB_evPencils).map (Pencil.toAff 2 60)) 10 11 120 12 60 88 1 1 50 10 = true := by decide
theorem cert_Bev_N2_m4 : certifyTarget 2 60 (nonParallel 2 branchB_evPencils) 1 10 11 120 12 60 88 = true :=
  cert_N2_of_6chunks' cert_Bev_N2_m4_h cert_Bev_N2_m4_0 cert_Bev_N2_m4_1 cert_Bev_N2_m4_2 cert_Bev_N2_m4_3 cert_Bev_N2_m4_4 cert_Bev_N2_m4_5

-- Family A even `s = 2t + 2` (`branchA_evPencils`): interior ≤ 30s + 21 = 1 + 60t + 80
theorem cert_Aev_Xa_in : certifyTarget 0 2 (nonParallel 0 branchA_evPencils) 1 18 23 4 2 60 80 = true := by decide
theorem cert_Aev_Xe_in : certifyTarget 0 2 (nonParallel 0 branchA_evPencils) 0 6 6 4 2 60 80 = true := by decide
theorem cert_Aev_S_in : certifyTarget 1 6 (nonParallel 1 branchA_evPencils) 0 16 20 12 3 60 80 = true := by decide
private theorem cert_Aev_N2_in_h : certifyHeader 2 60 (nonParallel 2 branchA_evPencils) 1 10 9 120 12 = true := by decide
private theorem cert_Aev_N2_in_0 : checkC0Range 120 ((nonParallel 2 branchA_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 80 1 1 0 10 = true := by decide
private theorem cert_Aev_N2_in_1 : checkC0Range 120 ((nonParallel 2 branchA_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 80 1 1 10 10 = true := by decide
private theorem cert_Aev_N2_in_2 : checkC0Range 120 ((nonParallel 2 branchA_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 80 1 1 20 10 = true := by decide
private theorem cert_Aev_N2_in_3 : checkC0Range 120 ((nonParallel 2 branchA_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 80 1 1 30 10 = true := by decide
private theorem cert_Aev_N2_in_4 : checkC0Range 120 ((nonParallel 2 branchA_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 80 1 1 40 10 = true := by decide
private theorem cert_Aev_N2_in_5 : checkC0Range 120 ((nonParallel 2 branchA_evPencils).map (Pencil.toAff 2 60)) 10 9 120 12 60 80 1 1 50 10 = true := by decide
theorem cert_Aev_N2_in : certifyTarget 2 60 (nonParallel 2 branchA_evPencils) 1 10 9 120 12 60 80 = true :=
  cert_N2_of_6chunks' cert_Aev_N2_in_h cert_Aev_N2_in_0 cert_Aev_N2_in_1 cert_Aev_N2_in_2 cert_Aev_N2_in_3 cert_Aev_N2_in_4 cert_Aev_N2_in_5

-- Family A odd `s = 2t + 3` (`branchA_oddPencils`): interior ≤ 30s + 21 = 1 + 60t + 110
theorem cert_Aodd_Xa_in : certifyTarget 0 2 (nonParallel 0 branchA_oddPencils) 0 18 32 4 2 60 110 = true := by decide
theorem cert_Aodd_Xe_in : certifyTarget 0 2 (nonParallel 0 branchA_oddPencils) 1 6 9 4 2 60 110 = true := by decide
theorem cert_Aodd_S_in : certifyTarget 1 6 (nonParallel 1 branchA_oddPencils) 0 16 28 12 3 60 110 = true := by decide
private theorem cert_Aodd_N2_in_h : certifyHeader 2 60 (nonParallel 2 branchA_oddPencils) 0 10 14 120 12 = true := by decide
private theorem cert_Aodd_N2_in_0 : checkC0Range 120 ((nonParallel 2 branchA_oddPencils).map (Pencil.toAff 2 60)) 10 14 120 12 60 110 1 0 0 10 = true := by decide
private theorem cert_Aodd_N2_in_1 : checkC0Range 120 ((nonParallel 2 branchA_oddPencils).map (Pencil.toAff 2 60)) 10 14 120 12 60 110 1 0 10 10 = true := by decide
private theorem cert_Aodd_N2_in_2 : checkC0Range 120 ((nonParallel 2 branchA_oddPencils).map (Pencil.toAff 2 60)) 10 14 120 12 60 110 1 0 20 10 = true := by decide
private theorem cert_Aodd_N2_in_3 : checkC0Range 120 ((nonParallel 2 branchA_oddPencils).map (Pencil.toAff 2 60)) 10 14 120 12 60 110 1 0 30 10 = true := by decide
private theorem cert_Aodd_N2_in_4 : checkC0Range 120 ((nonParallel 2 branchA_oddPencils).map (Pencil.toAff 2 60)) 10 14 120 12 60 110 1 0 40 10 = true := by decide
private theorem cert_Aodd_N2_in_5 : checkC0Range 120 ((nonParallel 2 branchA_oddPencils).map (Pencil.toAff 2 60)) 10 14 120 12 60 110 1 0 50 10 = true := by decide
theorem cert_Aodd_N2_in : certifyTarget 2 60 (nonParallel 2 branchA_oddPencils) 0 10 14 120 12 60 110 = true :=
  cert_N2_of_6chunks' cert_Aodd_N2_in_h cert_Aodd_N2_in_0 cert_Aodd_N2_in_1 cert_Aodd_N2_in_2 cert_Aodd_N2_in_3 cert_Aodd_N2_in_4 cert_Aodd_N2_in_5

/-- Consolidated interior line-count bounds for `familyB s` (`s ≥ 1`). -/
private lemma familyB_interior_le {s : ℕ} (hs : 1 ≤ s) :
    (∀ c ∈ parityRange (9 * s + 9), 0 ≤ c → c ≤ 9 * (s : ℤ) + 7 →
      projLineCount (familyB s) (1, 0, c) ≤ 30 * s + 28) ∧
    (∀ c ∈ parityRange (3 * s + 2), 0 ≤ c → c ≤ 3 * (s : ℤ) →
      projLineCount (familyB s) (1, 0, c) ≤ 30 * s + 28) ∧
    (∀ c ∈ parityRange (3 * s + 2), 0 ≤ c →
      projLineCount (familyB s) (1, 0, c) ≤ 30 * s + 30) ∧
    (∀ c ∈ parityRange (8 * s + 8), 0 ≤ c → c ≤ 8 * (s : ℤ) + 6 →
      projLineCount (familyB s) (1, 1, c) ≤ 30 * s + 28) ∧
    (∀ c ∈ parityRange (5 * s + 5), 0 ≤ c → c ≤ 5 * (s : ℤ) - 1 →
      projLineCount (familyB s) (1, 2, c) ≤ 30 * s + 28) ∧
    (∀ c ∈ parityRange (5 * s + 5), 0 ≤ c → c ≤ 5 * (s : ℤ) + 1 →
      projLineCount (familyB s) (1, 2, c) ≤ 30 * s + 29) := by
  rcases Nat.even_or_odd s with ⟨t', ht'⟩ | ⟨t, rfl⟩
  · have ht1 : 1 ≤ t' := by omega
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, t' = t + 1 := ⟨t' - 1, by omega⟩
    have hs_eq : s = 2 * t + 2 := by omega
    subst hs_eq
    have hXeq : familyB (2 * t + 2) =
        knightSet (18 * t + 27) (6 * t + 8) (16 * t + 24) (10 * t + 15) := by
      unfold familyB; congr 1 <;> omega
    have hcov : ∀ q0 : ℤ, ∀ x ∈ familyB (2 * t + 2), x.2.1 - q0 * x.1 = 0 ∨
        ∃ P ∈ nonParallel q0 branchB_evPencils, P.Mem t x := by
      intro q0 x hx
      rw [hXeq] at hx
      exact knightSet_covered_by_pencils (by omega) (by omega) (by omega) (by omega) x hx
    have hprop : Proper (familyB (2 * t + 2)) := knightSet_proper ..
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyB (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_left _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bev_Xa_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyB (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bev_Xe_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0
      have hp : (1, 0, c) ∈ familyB (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bev_Xe_top hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 1, c) ∈ familyB (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bev_S_in hprop (hcov 1) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 2, c) ∈ familyB (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bev_N2_in hprop (hcov 2) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 2, c) ∈ familyB (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bev_N2_m4 hprop (hcov 2) hp
        hc0 (by push_cast; omega) (by omega)
      omega
  · have hXeq : familyB (2 * t + 1) =
        knightSet (18 * t + 18) (6 * t + 5) (16 * t + 16) (10 * t + 10) := by
      unfold familyB; congr 1 <;> omega
    have hcov : ∀ q0 : ℤ, ∀ x ∈ familyB (2 * t + 1), x.2.1 - q0 * x.1 = 0 ∨
        ∃ P ∈ nonParallel q0 branch3Pencils, P.Mem t x := by
      intro q0 x hx
      rw [hXeq] at hx
      exact knightSet_covered_by_pencils (by omega) (by omega) (by omega) (by omega) x hx
    have hprop : Proper (familyB (2 * t + 1)) := knightSet_proper ..
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyB (2 * t + 1) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_left _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bodd_Xa_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyB (2 * t + 1) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bodd_Xe_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0
      have hp : (1, 0, c) ∈ familyB (2 * t + 1) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bodd_Xe_top hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 1, c) ∈ familyB (2 * t + 1) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bodd_S_in hprop (hcov 1) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 2, c) ∈ familyB (2 * t + 1) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bodd_N2_in hprop (hcov 2) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 2, c) ∈ familyB (2 * t + 1) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Bodd_N2_m4 hprop (hcov 2) hp
        hc0 (by push_cast; omega) (by omega)
      omega

/-- Consolidated interior line-count bounds for `familyA s` (`s ≥ 2`). -/
private lemma familyA_interior_le {s : ℕ} (hs : 2 ≤ s) :
    (∀ c ∈ parityRange (9 * s + 7), 0 ≤ c → c ≤ 9 * (s : ℤ) + 5 →
      projLineCount (familyA s) (1, 0, c) ≤ 30 * s + 21) ∧
    (∀ c ∈ parityRange (3 * s + 2), 0 ≤ c → c ≤ 3 * (s : ℤ) →
      projLineCount (familyA s) (1, 0, c) ≤ 30 * s + 21) ∧
    (∀ c ∈ parityRange (8 * s + 6), 0 ≤ c → c ≤ 8 * (s : ℤ) + 4 →
      projLineCount (familyA s) (1, 1, c) ≤ 30 * s + 21) ∧
    (∀ c ∈ parityRange (5 * s + 3), 0 ≤ c → c ≤ 5 * (s : ℤ) - 1 →
      projLineCount (familyA s) (1, 2, c) ≤ 30 * s + 21) := by
  rcases Nat.even_or_odd s with ⟨t', ht'⟩ | ⟨t', ht'⟩
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, t' = t + 1 := ⟨t' - 1, by omega⟩
    have hs_eq : s = 2 * t + 2 := by omega
    subst hs_eq
    have hXeq : familyA (2 * t + 2) =
        knightSet (18 * t + 25) (6 * t + 8) (16 * t + 22) (10 * t + 13) := by
      unfold familyA; congr 1 <;> omega
    have hcov : ∀ q0 : ℤ, ∀ x ∈ familyA (2 * t + 2), x.2.1 - q0 * x.1 = 0 ∨
        ∃ P ∈ nonParallel q0 branchA_evPencils, P.Mem t x := by
      intro q0 x hx
      rw [hXeq] at hx
      exact knightSet_covered_by_pencils (by omega) (by omega) (by omega) (by omega) x hx
    have hprop : Proper (familyA (2 * t + 2)) := knightSet_proper ..
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyA (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_left _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aev_Xa_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyA (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aev_Xe_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 1, c) ∈ familyA (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aev_S_in hprop (hcov 1) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 2, c) ∈ familyA (2 * t + 2) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aev_N2_in hprop (hcov 2) hp
        hc0 (by push_cast; omega) (by omega)
      omega
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, t' = t + 1 := ⟨t' - 1, by omega⟩
    have hs_eq : s = 2 * t + 3 := by omega
    subst hs_eq
    have hXeq : familyA (2 * t + 3) =
        knightSet (18 * t + 34) (6 * t + 11) (16 * t + 30) (10 * t + 18) := by
      unfold familyA; congr 1 <;> omega
    have hcov : ∀ q0 : ℤ, ∀ x ∈ familyA (2 * t + 3), x.2.1 - q0 * x.1 = 0 ∨
        ∃ P ∈ nonParallel q0 branchA_oddPencils, P.Mem t x := by
      intro q0 x hx
      rw [hXeq] at hx
      exact knightSet_covered_by_pencils (by omega) (by omega) (by omega) (by omega) x hx
    have hprop : Proper (familyA (2 * t + 3)) := knightSet_proper ..
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyA (2 * t + 3) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_left _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aodd_Xa_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 0, c) ∈ familyA (2 * t + 3) :=
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aodd_Xe_in hprop (hcov 0) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 1, c) ∈ familyA (2 * t + 3) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aodd_S_in hprop (hcov 1) hp
        hc0 (by push_cast; omega) (by omega)
      omega
    · intro c hc hc0 hchi
      have hp : (1, 2, c) ∈ familyA (2 * t + 3) :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      rw [mem_parityRange_iff] at hc
      have h := projLineCount_le_of_certifyTarget cert_Aodd_N2_in hprop (hcov 2) hp
        hc0 (by push_cast; omega) (by omega)
      omega

/-! #### Ordinary-Line Verification Helper for `knightSet` -/

private lemma knight_isOrd {a e b m : ℕ} {p q : Pt}
    (h1a : ∀ c : ℤ, -(a : ℤ) ≤ c → c ≤ a → c % 2 = (a : ℤ) % 2 → det p q (1, 0, c) = 0 →
      (1, 0, c) = p ∨ (1, 0, c) = q)
    (h1e : ∀ c : ℤ, -(e : ℤ) ≤ c → c ≤ e → c % 2 = (e : ℤ) % 2 → det p q (1, 0, c) = 0 →
      (1, 0, c) = p ∨ (1, 0, c) = q)
    (h2a : ∀ c : ℤ, -(a : ℤ) ≤ c → c ≤ a → c % 2 = (a : ℤ) % 2 → det p q (0, 1, c) = 0 →
      (0, 1, c) = p ∨ (0, 1, c) = q)
    (h2e : ∀ c : ℤ, -(e : ℤ) ≤ c → c ≤ e → c % 2 = (e : ℤ) % 2 → det p q (0, 1, c) = 0 →
      (0, 1, c) = p ∨ (0, 1, c) = q)
    (h3 : ∀ c : ℤ, -(b : ℤ) ≤ c → c ≤ b → c % 2 = (b : ℤ) % 2 → det p q (1, 1, c) = 0 →
      (1, 1, c) = p ∨ (1, 1, c) = q)
    (h4 : ∀ c : ℤ, -(b : ℤ) ≤ c → c ≤ b → c % 2 = (b : ℤ) % 2 → det p q (1, -1, c) = 0 →
      (1, -1, c) = p ∨ (1, -1, c) = q)
    (h5 : ∀ c : ℤ, -(m : ℤ) ≤ c → c ≤ m → c % 2 = (m : ℤ) % 2 → det p q (1, 2, c) = 0 →
      (1, 2, c) = p ∨ (1, 2, c) = q)
    (h6 : ∀ c : ℤ, -(m : ℤ) ≤ c → c ≤ m → c % 2 = (m : ℤ) % 2 → det p q (1, -2, c) = 0 →
      (1, -2, c) = p ∨ (1, -2, c) = q)
    (h7 : ∀ c : ℤ, -(m : ℤ) ≤ c → c ≤ m → c % 2 = (m : ℤ) % 2 → det p q (2, 1, c) = 0 →
      (2, 1, c) = p ∨ (2, 1, c) = q)
    (h8 : ∀ c : ℤ, -(m : ℤ) ≤ c → c ≤ m → c % 2 = (m : ℤ) % 2 → det p q (2, -1, c) = 0 →
      (2, -1, c) = p ∨ (2, -1, c) = q)
    (h9 : det p q (0, 0, 1) = 0 → (0, 0, 1) = p ∨ (0, 0, 1) = q) :
    IsOrdinaryLine (knightSet a e b m) p q := by
  intro r hr hdet
  rcases mem_knightSet_iff.mp hr with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
  · rcases Finset.mem_union.mp hc with h | h
    · rw [mem_parityRange_iff] at h; exact h1a c h.1 h.2.1 h.2.2 hdet
    · rw [mem_parityRange_iff] at h; exact h1e c h.1 h.2.1 h.2.2 hdet
  · rcases Finset.mem_union.mp hc with h | h
    · rw [mem_parityRange_iff] at h; exact h2a c h.1 h.2.1 h.2.2 hdet
    · rw [mem_parityRange_iff] at h; exact h2e c h.1 h.2.1 h.2.2 hdet
  · rw [mem_parityRange_iff] at hc; exact h3 c hc.1 hc.2.1 hc.2.2 hdet
  · rw [mem_parityRange_iff] at hc; exact h4 c hc.1 hc.2.1 hc.2.2 hdet
  · rw [mem_parityRange_iff] at hc; exact h5 c hc.1 hc.2.1 hc.2.2 hdet
  · rw [mem_parityRange_iff] at hc; exact h6 c hc.1 hc.2.1 hc.2.2 hdet
  · rw [mem_parityRange_iff] at hc; exact h7 c hc.1 hc.2.1 hc.2.2 hdet
  · rw [mem_parityRange_iff] at hc; exact h8 c hc.1 hc.2.1 hc.2.2 hdet
  · exact h9 hdet

private lemma knight_ord_solve {a e b m : ℕ} {p q : Pt}
    (h : ∀ u v c : ℤ,
      ((u = 1 ∧ v = 0 ∧ ((-(a : ℤ) ≤ c ∧ c ≤ a ∧ c % 2 = (a : ℤ) % 2) ∨
                         (-(e : ℤ) ≤ c ∧ c ≤ e ∧ c % 2 = (e : ℤ) % 2))) ∨
       (u = 0 ∧ v = 1 ∧ ((-(a : ℤ) ≤ c ∧ c ≤ a ∧ c % 2 = (a : ℤ) % 2) ∨
                         (-(e : ℤ) ≤ c ∧ c ≤ e ∧ c % 2 = (e : ℤ) % 2))) ∨
       (u = 1 ∧ v = 1 ∧ -(b : ℤ) ≤ c ∧ c ≤ b ∧ c % 2 = (b : ℤ) % 2) ∨
       (u = 1 ∧ v = -1 ∧ -(b : ℤ) ≤ c ∧ c ≤ b ∧ c % 2 = (b : ℤ) % 2) ∨
       (u = 1 ∧ v = 2 ∧ -(m : ℤ) ≤ c ∧ c ≤ m ∧ c % 2 = (m : ℤ) % 2) ∨
       (u = 1 ∧ v = -2 ∧ -(m : ℤ) ≤ c ∧ c ≤ m ∧ c % 2 = (m : ℤ) % 2) ∨
       (u = 2 ∧ v = 1 ∧ -(m : ℤ) ≤ c ∧ c ≤ m ∧ c % 2 = (m : ℤ) % 2) ∨
       (u = 2 ∧ v = -1 ∧ -(m : ℤ) ≤ c ∧ c ≤ m ∧ c % 2 = (m : ℤ) % 2) ∨
       (u = 0 ∧ v = 0 ∧ c = 1)) →
      det p q (u, v, c) = 0 → (u, v, c) = p ∨ (u, v, c) = q) :
    IsOrdinaryLine (knightSet a e b m) p q :=
  knight_isOrd
    (fun c h1 h2 h3 hd => h 1 0 c (Or.inl ⟨rfl, rfl, Or.inl ⟨h1, h2, h3⟩⟩) hd)
    (fun c h1 h2 h3 hd => h 1 0 c (Or.inl ⟨rfl, rfl, Or.inr ⟨h1, h2, h3⟩⟩) hd)
    (fun c h1 h2 h3 hd => h 0 1 c (Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨h1, h2, h3⟩⟩)) hd)
    (fun c h1 h2 h3 hd => h 0 1 c (Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨h1, h2, h3⟩⟩)) hd)
    (fun c h1 h2 h3 hd => h 1 1 c (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2, h3⟩))) hd)
    (fun c h1 h2 h3 hd => h 1 (-1) c (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2, h3⟩)))) hd)
    (fun c h1 h2 h3 hd => h 1 2 c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2, h3⟩))))) hd)
    (fun c h1 h2 h3 hd => h 1 (-2) c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2, h3⟩)))))) hd)
    (fun c h1 h2 h3 hd => h 2 1 c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2, h3⟩))))))) hd)
    (fun c h1 h2 h3 hd => h 2 (-1) c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1, h2, h3⟩)))))))) hd)
    (fun hd => h 0 0 1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))))) hd)

/-- Ordinary-line helper: proves `IsOrdinaryLine (familyB s) p q` for any of the 18 boundary pairs (`s ≥ 1`). -/
private lemma familyB_isOrd {s : ℕ} (hs : 1 ≤ s) {p q : Pt}
    (hpq :
      (p = (1, 0, 9 * (s : ℤ) + 9) ∧
        (q = (1, 2, -(5 * (s : ℤ) + 3)) ∨ q = (1, -2, -(5 * (s : ℤ) + 3)) ∨
         q = (2, 1, -(5 * (s : ℤ) + 3)) ∨ q = (2, -1, -(5 * (s : ℤ) + 3)))) ∨
      (p = (0, 1, 9 * (s : ℤ) + 9) ∧ q = (1, 2, -(5 * (s : ℤ) + 3))) ∨
      (p = (1, 0, 3 * (s : ℤ) + 2) ∧
        (q = (1, 2, -(5 * (s : ℤ) + 3)) ∨ q = (1, -2, -(5 * (s : ℤ) + 3)))) ∨
      (p = (1, 1, 8 * (s : ℤ) + 8) ∧
        (q = (1, 2, -(5 * (s : ℤ) + 3)) ∨ q = (1, -2, 5 * (s : ℤ) + 3) ∨
         q = (2, 1, -(5 * (s : ℤ) + 3)) ∨ q = (2, -1, -(5 * (s : ℤ) + 3)))) ∨
      (p = (1, 2, 5 * (s : ℤ) + 5) ∧
        (q = (1, -2, 5 * (s : ℤ) + 3) ∨ q = (2, 1, -(5 * (s : ℤ) + 3)) ∨
         q = (2, -1, 5 * (s : ℤ) + 3) ∨ q = (2, -1, -(5 * (s : ℤ) + 3)))) ∨
      (p = (2, 1, 5 * (s : ℤ) + 5) ∧ q = (1, 2, -(5 * (s : ℤ) + 3))) ∨
      (p = (2, 1, 5 * (s : ℤ) + 3) ∧ q = (1, -2, 5 * (s : ℤ) + 3)) ∨
      (p = (1, 2, 5 * (s : ℤ) + 1) ∧ q = (1, -2, 5 * (s : ℤ) + 3))) :
    IsOrdinaryLine (familyB s) p q := by
  unfold familyB
  refine knight_ord_solve (fun u v c hmem hd => ?_)
  rcases hpq with ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  (rcases hmem with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, rfl⟩ <;>
   simp only [det] at hd <;>
   first
   | (exfalso; omega)
   | (left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
   | (right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))))

/-- Ordinary-line helper: proves `IsOrdinaryLine (familyA s) p q` for any of the 19 boundary pairs (`s ≥ 2`). -/
private lemma familyA_isOrd {s : ℕ} (hs : 2 ≤ s) {p q : Pt}
    (hpq :
      (p = (1, 0, 9 * (s : ℤ) + 7) ∧
        (q = (1, 2, -(5 * (s : ℤ) + 1)) ∨ q = (1, -2, -(5 * (s : ℤ) + 1)) ∨
         q = (2, 1, -(5 * (s : ℤ) + 1)) ∨ q = (2, -1, -(5 * (s : ℤ) + 1)))) ∨
      (p = (0, 1, 9 * (s : ℤ) + 7) ∧ q = (1, 2, -(5 * (s : ℤ) + 1))) ∨
      (p = (1, 0, 3 * (s : ℤ) + 2) ∧
        (q = (1, 2, -(5 * (s : ℤ) + 1)) ∨ q = (1, -2, -(5 * (s : ℤ) + 1)) ∨
         q = (2, 1, -(5 * (s : ℤ) + 1)) ∨ q = (2, -1, -(5 * (s : ℤ) + 1)))) ∨
      (p = (0, 1, 3 * (s : ℤ) + 2) ∧ q = (1, 2, -(5 * (s : ℤ) + 1))) ∨
      (p = (1, 1, 8 * (s : ℤ) + 6) ∧
        (q = (1, 2, -(5 * (s : ℤ) + 1)) ∨ q = (1, -2, 5 * (s : ℤ) + 1) ∨
         q = (2, 1, -(5 * (s : ℤ) + 1)) ∨ q = (2, -1, -(5 * (s : ℤ) + 1)))) ∨
      (p = (1, 2, 5 * (s : ℤ) + 3) ∧
        (q = (1, -2, 5 * (s : ℤ) + 1) ∨ q = (2, 1, -(5 * (s : ℤ) + 1)) ∨
         q = (2, -1, -(5 * (s : ℤ) + 1)))) ∨
      (p = (2, 1, 5 * (s : ℤ) + 3) ∧ q = (1, 2, -(5 * (s : ℤ) + 1))) ∨
      (p = (2, 1, 5 * (s : ℤ) + 1) ∧ q = (1, -2, 5 * (s : ℤ) + 1))) :
    IsOrdinaryLine (familyA s) p q := by
  unfold familyA
  refine knight_ord_solve (fun u v c hmem hd => ?_)
  rcases hpq with ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  (rcases hmem with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, rfl⟩ <;>
   simp only [det] at hd <;>
   first
   | (exfalso; omega)
   | (left; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega)))
   | (right; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))))

/-! #### Upper Bounds and Exact Tightness for `C = B \ D_8`, `E4 = B \ D_4`, `A \ D_8`, `A \ D_4` -/

/-- **Upper Bound for `Family C` Family C (`s ≥ 1`)**: every point of `familyC s` lies on at most
`30s + 28 = (n - 5) / 2` spanned lines. -/
theorem familyC_lineCount_le {s : ℕ} (hs : 1 ≤ s) :
    ∀ p ∈ familyC s, projLineCount (familyC s) p ≤ 30 * s + 28 := by
  set m2 : ℤ := 5 * (s : ℤ) + 3
  have hDsub : knightD8 m2 ⊆ familyB s := by
    have heq : m2 = (((5 * s + 5 : ℕ) : ℤ) - 2) := by unfold m2; push_cast; ring
    rw [heq]; exact knightD8_subset_knightSet (by omega)
  have hsymZ : ∀ p ∈ familyC s, projLineCount (familyC s) (symZ p) = projLineCount (familyC s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symZ_props (9 * s + 9) (3 * s + 2) (8 * s + 8) (5 * s + 5)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD8_symZ h2 h3 hp
  have hsymY : ∀ p ∈ familyC s, projLineCount (familyC s) (symY p) = projLineCount (familyC s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symY_props (9 * s + 9) (3 * s + 2) (8 * s + 8) (5 * s + 5)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD8_symY h2 h3 hp
  have hsymXY : ∀ p ∈ familyC s, projLineCount (familyC s) (symXY p) = projLineCount (familyC s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symXY_props (9 * s + 9) (3 * s + 2) (8 * s + 8) (5 * s + 5)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD8_symXY h2 h3 hp
  obtain ⟨hXa_in, hXe_in, hXe_top, hS_in, hN2_in, hN2_m4⟩ := familyB_interior_le hs
  have hdrop : ∀ {p : Pt} (hpB : p ∈ familyB s) (W : Finset Pt),
      W ⊆ knightD8 m2 → p ∉ W → (∀ q ∈ W, IsOrdinaryLine (familyB s) p q) →
      projLineCount (familyC s) p + W.card ≤ projLineCount (familyB s) p := by
    intro p hpB W hWD hpW hord
    exact projLineCount_sdiff_le_sub (knightSet_proper ..) hpB hWD
      (fun q hq => Finset.mem_erase.mpr ⟨fun heq => hpW (heq ▸ hq), hDsub (hWD hq)⟩) hord
  have hpos_axis : ∀ c ∈ parityRange (9 * s + 9) ∪ parityRange (3 * s + 2), 0 ≤ c →
      projLineCount (familyC s) (1, 0, c) ≤ 30 * s + 28 := by
    intro c hc hc0
    rcases Finset.mem_union.mp hc with hca | hce
    · have hca' := mem_parityRange_iff.mp hca
      by_cases htop : c = 9 * (s : ℤ) + 9
      · subst htop
        have hpB : (1, 0, 9 * (s : ℤ) + 9) ∈ familyB s :=
          mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ hca, rfl⟩)
        let W : Finset Pt := {(1, 2, -m2), (1, -2, -m2), (2, 1, -m2), (2, -1, -m2)}
        have hWc : W.card = 4 := by
          unfold W
          rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
              Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        have hd := hdrop hpB W
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl <;> simp [knightD8])
          (by simp [W])
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl
              · exact familyB_isOrd hs (Or.inl ⟨rfl, Or.inl rfl⟩)
              · exact familyB_isOrd hs (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
              · exact familyB_isOrd hs (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)
              · exact familyB_isOrd hs (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩))
        have hbd := familyB_lineCount_le s _ hpB
        omega
      · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hXa_in c hca hc0 (by omega))
    · have hce' := mem_parityRange_iff.mp hce
      by_cases htop : c = 3 * (s : ℤ) + 2
      · subst htop
        have hpB : (1, 0, 3 * (s : ℤ) + 2) ∈ familyB s :=
          mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_right _ hce, rfl⟩)
        let W : Finset Pt := {(1, 2, -m2), (1, -2, -m2)}
        have hWc : W.card = 2 := by
          unfold W; rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        have hd := hdrop hpB W
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl <;> simp [knightD8])
          (by simp [W])
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl
              · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))
              · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))))
        have hbd := hXe_top _ hce hc0
        omega
      · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hXe_in c hce hc0 (by omega))
  have hall_axis : ∀ c ∈ parityRange (9 * s + 9) ∪ parityRange (3 * s + 2),
      (1, 0, c) ∈ familyC s → projLineCount (familyC s) (1, 0, c) ≤ 30 * s + 28 := by
    intro c hc hmem
    by_cases h0 : 0 ≤ c
    · exact hpos_axis c hc h0
    · have hnc : -c ∈ parityRange (9 * s + 9) ∪ parityRange (3 * s + 2) := by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_left _ (neg_mem_parityRange h)
        · exact Finset.mem_union_right _ (neg_mem_parityRange h)
      have hsZ : symZ (1, 0, c) = (1, 0, -c) := by simp [symZ, negZ]
      rw [← hsymZ _ hmem, hsZ]
      exact hpos_axis (-c) hnc (by omega)
  have hpos_diag : ∀ c ∈ parityRange (8 * s + 8), 0 ≤ c →
      projLineCount (familyC s) (1, 1, c) ≤ 30 * s + 28 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 8 * (s : ℤ) + 8
    · subst htop
      have hpB : (1, 1, 8 * (s : ℤ) + 8) ∈ familyB s :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))
      let W : Finset Pt := {(1, 2, -m2), (1, -2, m2), (2, 1, -m2), (2, -1, -m2)}
      have hWc : W.card = 4 := by
        unfold W
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
      have hd := hdrop hpB W
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl <;> simp [knightD8])
        (by simp [W])
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩))))
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩))))
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩)))))
      have hbd := familyB_lineCount_le s _ hpB
      omega
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hS_in c hc hc0 (by omega))
  have hall_diag : ∀ c ∈ parityRange (8 * s + 8),
      (1, 1, c) ∈ familyC s → projLineCount (familyC s) (1, 1, c) ≤ 30 * s + 28 := by
    intro c hc hmem
    by_cases h0 : 0 ≤ c
    · exact hpos_diag c hc h0
    · have hsZ : symZ (1, 1, c) = (1, 1, -c) := by simp [symZ, negZ]
      rw [← hsymZ _ hmem, hsZ]
      exact hpos_diag (-c) (neg_mem_parityRange hc) (by omega)
  have hpos_kn : ∀ c ∈ parityRange (5 * s + 5), 0 ≤ c →
      (1, 2, c) ∈ familyC s → projLineCount (familyC s) (1, 2, c) ≤ 30 * s + 28 := by
    intro c hc hc0 hmem
    have hc' := mem_parityRange_iff.mp hc
    have hnot_m2 : c ≠ 5 * (s : ℤ) + 3 := by
      intro heq; subst heq
      exact (Finset.mem_sdiff.mp hmem).2 (by simp [knightD8])
    by_cases htop : c = 5 * (s : ℤ) + 5
    · subst htop
      have hpB : (1, 2, 5 * (s : ℤ) + 5) ∈ familyB s :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))))
      let W : Finset Pt := {(1, -2, m2), (2, 1, -m2), (2, -1, m2), (2, -1, -m2)}
      have hWc : W.card = 4 := by
        unfold W
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
            Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have hd := hdrop hpB W
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl <;> simp [knightD8])
        (by simp [W])
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))))
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)))))
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))))
            · exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩))))))
      have hbd := familyB_lineCount_le s _ hpB
      omega
    · by_cases hm4 : c = 5 * (s : ℤ) + 1
      · subst hm4
        have hpB : (1, 2, 5 * (s : ℤ) + 1) ∈ familyB s :=
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))))
        let W : Finset Pt := {(1, -2, m2)}
        have hWc : W.card = 1 := Finset.card_singleton _
        have hd := hdrop hpB W
          (by intro q hq; rw [Finset.mem_singleton.mp hq]; simp [knightD8])
          (by simp [W])
          (by intro q hq; rw [Finset.mem_singleton.mp hq]
              exact familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))))
        have hbd := hN2_m4 _ hc hc0 (by omega)
        omega
      · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hN2_in c hc hc0 (by omega))
  have hall_kn : ∀ c ∈ parityRange (5 * s + 5),
      (1, 2, c) ∈ familyC s → projLineCount (familyC s) (1, 2, c) ≤ 30 * s + 28 := by
    intro c hc hmem
    by_cases h0 : 0 ≤ c
    · exact hpos_kn c hc h0 hmem
    · have hsZ : symZ (1, 2, c) = (1, 2, -c) := by simp [symZ, negZ]
      have hmem' : (1, 2, -c) ∈ familyC s := by
        rw [← hsZ]
        refine Finset.mem_sdiff.mpr ⟨(knightSet_symZ_props ..).1 _ (Finset.mem_sdiff.mp hmem).1, ?_⟩
        intro hD
        have := knightD8_symZ _ hD
        rw [hsZ, show symZ (1, 2, -c) = (1, 2, c) by simp [symZ, negZ]] at this
        exact (Finset.mem_sdiff.mp hmem).2 this
      rw [← hsymZ _ hmem, hsZ]
      exact hpos_kn (-c) (neg_mem_parityRange hc) (by omega) hmem'
  intro p hp
  have hpB := (Finset.mem_sdiff.mp hp).1
  rcases mem_knightSet_iff.mp hpB with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
  · exact hall_axis c hc hp
  · have hsXY : symXY (0, 1, c) = (1, 0, c) := by simp [symXY, swapXY]
    have hp' : (1, 0, c) ∈ familyC s := Finset.mem_sdiff.mpr
      ⟨mem_knightSet_iff.mpr (Or.inl ⟨c, hc, rfl⟩), by simp [knightD8]⟩
    rw [← hsymXY _ hp, hsXY]; exact hall_axis c hc hp'
  · exact hall_diag c hc hp
  · have hsY : symY (1, -1, c) = (1, 1, c) := by simp [symY, negY]
    have hp' : (1, 1, c) ∈ familyC s := Finset.mem_sdiff.mpr
      ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))), by simp [knightD8]⟩
    rw [← hsymY _ hp, hsY]; exact hall_diag c hc hp'
  · exact hall_kn c hc hp
  · have hsY : symY (1, -2, c) = (1, 2, c) := by simp [symY, negY]
    have hp' : (1, 2, c) ∈ familyC s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp).2 (by simpa [symY, negY] using knightD8_symY _ hD)
    rw [← hsymY _ hp, hsY]; exact hall_kn c hc hp'
  · have hsXY : symXY (2, 1, c) = (1, 2, c) := by simp [symXY, swapXY]
    have hp' : (1, 2, c) ∈ familyC s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp).2 (by simpa [symXY, swapXY] using knightD8_symXY _ hD)
    rw [← hsymXY _ hp, hsXY]; exact hall_kn c hc hp'
  · have hsY : symY (2, -1, c) = (2, 1, c) := by simp [symY, negY]
    have hp1 : (2, 1, c) ∈ familyC s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp).2 (by simpa [symY, negY] using knightD8_symY _ hD)
    have hsXY : symXY (2, 1, c) = (1, 2, c) := by simp [symXY, swapXY]
    have hp2 : (1, 2, c) ∈ familyC s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp1).2 (by simpa [symXY, swapXY] using knightD8_symXY _ hD)
    rw [← hsymY _ hp, hsY, ← hsymXY _ hp1, hsXY]; exact hall_kn c hc hp2
  · exact (projLineCount_subset_le Finset.sdiff_subset _).trans
      ((knightSet_lineCount_origin ..).trans (by omega))

/-- **Exact Tightness for `Family C` Family C (`s ≥ 1`)**: `(1, 0, 9s + 9)` lies on **exactly**
`30s + 28` spanned lines of `familyC s`. -/
theorem familyC_top_lineCount {s : ℕ} (hs : 1 ≤ s) :
    projLineCount (familyC s) (1, 0, ((9 * s + 9 : ℕ) : ℤ)) = 30 * s + 28 := by
  classical
  set p0 : Pt := (1, 0, ((9 * s + 9 : ℕ) : ℤ))
  set m2 : ℤ := 5 * (s : ℤ) + 3
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hpB : p0 ∈ familyB s := mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  have hpC : p0 ∈ familyC s := Finset.mem_sdiff.mpr ⟨hpB, by simp [p0, knightD8]⟩
  have hle : projLineCount (familyC s) p0 ≤ 30 * s + 28 := familyC_lineCount_le hs p0 hpC
  -- Every deleted point with +m2 is collinear with p0 and a surviving point of familyC s,
  -- so spannedProjLines (familyB s) p0 ⊆ spannedProjLines (familyC s) p0 ∪ W4.image (projLine p0).
  let W4 : Finset Pt := {(1, 2, -m2), (1, -2, -m2), (2, 1, -m2), (2, -1, -m2)}
  have hW4_card : W4.card = 4 := by
    unfold W4; repeat (rw [Finset.card_insert_of_notMem (by simp)]); simp
  have hsub : spannedProjLines (familyB s) p0 ⊆
      spannedProjLines (familyC s) p0 ∪ W4.image (projLine p0) := by
    intro l hl
    simp only [spannedProjLines, Finset.mem_image, Finset.mem_erase] at hl
    rcases hl with ⟨q, ⟨hqne, hqB⟩, rfl⟩
    by_cases hqD : q ∈ knightD8 m2
    · simp only [knightD8, Finset.mem_insert, Finset.mem_singleton] at hqD
      have hpropB : Proper (familyB s) := knightSet_proper ..
      have hns_q : ¬ SamePt p0 q := fun hs' => hqne (hpropB.2 p0 hpB q hqB hs').symm
      have hcover : ∀ r : Pt, r ∈ familyC s → r ≠ p0 → det p0 q r = 0 →
          projLine p0 q ∈ spannedProjLines (familyC s) p0 ∪ W4.image (projLine p0) := by
        intro r hrC hrne hdet
        have hrB : r ∈ familyB s := (Finset.mem_sdiff.mp hrC).1
        have hns_r : ¬ SamePt p0 r := fun hs' => hrne (hpropB.2 p0 hpB r hrB hs').symm
        have hleq : projLine p0 q = projLine p0 r :=
          (projLine_eq_iff_det_eq_zero (hpropB.1 p0 hpB) (hpropB.1 q hqB) (hpropB.1 r hrB) hns_q hns_r).mpr hdet
        rw [hleq]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hrne, hrC⟩))
      rcases hqD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- (1, 2, m2) collinear with p0 and (0, 1, -(2s+3))
        have hy : -(2 * (s : ℤ) + 3) ∈ parityRange (9 * s + 9) ∪ parityRange (3 * s + 2) := by
          by_cases hpar : (9 * (s : ℤ) + 9) % 2 = 1
          · exact Finset.mem_union_left _ (mem_parityRange_iff.mpr (by omega))
          · exact Finset.mem_union_right _ (mem_parityRange_iff.mpr (by omega))
        exact hcover (0, 1, -(2 * (s : ℤ) + 3))
          (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, hy, rfl⟩)), by simp [knightD8]⟩)
          (by simp [p0]) (by unfold p0 m2 det; push_cast; ring)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [W4]))
      · -- (1, -2, m2) collinear with p0 and (0, 1, 2s+3)
        have hy : (2 * (s : ℤ) + 3) ∈ parityRange (9 * s + 9) ∪ parityRange (3 * s + 2) := by
          by_cases hpar : (9 * (s : ℤ) + 9) % 2 = 1
          · exact Finset.mem_union_left _ (mem_parityRange_iff.mpr (by omega))
          · exact Finset.mem_union_right _ (mem_parityRange_iff.mpr (by omega))
        exact hcover (0, 1, 2 * (s : ℤ) + 3)
          (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, hy, rfl⟩)), by simp [knightD8]⟩)
          (by simp [p0]) (by unfold p0 m2 det; push_cast; ring)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [W4]))
      · -- (2, 1, m2) collinear with p0 and (1, 1, -(4s+6))
        have hd : -(4 * (s : ℤ) + 6) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
        exact hcover (1, 1, -(4 * (s : ℤ) + 6))
          (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hd, rfl⟩))), by simp [knightD8]⟩)
          (by simp [p0]) (by unfold p0 m2 det; push_cast; ring)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [W4]))
      · -- (2, -1, m2) collinear with p0 and (1, -1, -(4s+6))
        have hd : -(4 * (s : ℤ) + 6) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
        exact hcover (1, -1, -(4 * (s : ℤ) + 6))
          (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hd, rfl⟩)))), by simp [knightD8]⟩)
          (by simp [p0]) (by unfold p0 m2 det; push_cast; ring)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [W4]))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (Finset.mem_erase.mpr ⟨hqne, Finset.mem_sdiff.mpr ⟨hqB, hqD⟩⟩))
  have hge : 30 * s + 28 ≤ projLineCount (familyC s) p0 := by
    have hBtop : projLineCount (familyB s) p0 = 30 * s + 32 := familyB_top_lineCount s
    have hcard := Finset.card_le_card hsub
    have hun := Finset.card_union_le (spannedProjLines (familyC s) p0) (W4.image (projLine p0))
    have himg : (W4.image (projLine p0)).card ≤ 4 := Finset.card_image_le.trans (le_of_eq hW4_card)
    change (spannedProjLines (familyB s) p0).card = 30 * s + 32 at hBtop
    change 30 * s + 28 ≤ (spannedProjLines (familyC s) p0).card
    omega
  exact le_antisymm hle hge

/-- **Upper Bound for `Family E4` Family E4 (`s ≥ 1`)**: every point of `familyBE4 s` lies on at most
`30s + 31 = G(60s + 65) - 1` spanned lines. -/
theorem familyBE4_lineCount_le {s : ℕ} (hs : 1 ≤ s) :
    ∀ p ∈ familyBE4 s, projLineCount (familyBE4 s) p ≤ 30 * s + 31 := by
  set m2 : ℤ := 5 * (s : ℤ) + 3
  have hDsub : knightD4 m2 ⊆ familyB s := by
    have heq : m2 = (((5 * s + 5 : ℕ) : ℤ) - 2) := by unfold m2; push_cast; ring
    rw [heq]; exact (knightD4_subset_knightD8 _).trans (knightD8_subset_knightSet (by omega))
  have hsymZ : ∀ p ∈ familyBE4 s, projLineCount (familyBE4 s) (symZ p) = projLineCount (familyBE4 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symZ_props (9 * s + 9) (3 * s + 2) (8 * s + 8) (5 * s + 5)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD4_symZ h2 h3 hp
  have hsymY : ∀ p ∈ familyBE4 s, projLineCount (familyBE4 s) (symY p) = projLineCount (familyBE4 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symY_props (9 * s + 9) (3 * s + 2) (8 * s + 8) (5 * s + 5)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD4_symY h2 h3 hp
  obtain ⟨hXa_in, _, hXe_top, hS_in, _, hN2_m4⟩ := familyB_interior_le hs
  have hdrop1 : ∀ {p q : Pt}, p ∈ familyB s → q ∈ knightD4 m2 → q ≠ p →
      IsOrdinaryLine (familyB s) p q → projLineCount (familyBE4 s) p ≤ 30 * s + 31 := by
    intro p q hpB hqD hqp hord
    have hsub := projLineCount_sdiff_le_sub (D := knightD4 m2) (W := {q}) (knightSet_proper ..) hpB
      (Finset.singleton_subset_iff.mpr hqD)
      (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨hqp, hDsub hqD⟩))
      (fun r hr => by rw [Finset.mem_singleton.mp hr]; exact hord)
    have hbd := familyB_lineCount_le s p hpB
    simp only [Finset.card_singleton] at hsub
    change projLineCount (familyBE4 s) p + 1 ≤ projLineCount (familyB s) p at hsub
    omega
  have hmemZ : ∀ p ∈ familyBE4 s, symZ p ∈ familyBE4 s := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨(knightSet_symZ_props ..).1 _ (Finset.mem_sdiff.mp hp).1, fun hD => ?_⟩
    have hD' := knightD4_symZ _ hD
    rw [(knightSet_symZ_props ..).2.1 _ (Finset.mem_sdiff.mp hp).1] at hD'
    exact (Finset.mem_sdiff.mp hp).2 hD'
  have hmemY : ∀ p ∈ familyBE4 s, symY p ∈ familyBE4 s := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨(knightSet_symY_props ..).1 _ (Finset.mem_sdiff.mp hp).1, fun hD => ?_⟩
    have hD' := knightD4_symY _ hD
    rw [(knightSet_symY_props ..).2.1 _ (Finset.mem_sdiff.mp hp).1] at hD'
    exact (Finset.mem_sdiff.mp hp).2 hD'
  have hB_symXY : ∀ p ∈ familyB s, projLineCount (familyB s) (symXY p) = projLineCount (familyB s) p :=
    fun _ hp => projLineCount_symXY hp
  have hB_symZ : ∀ p ∈ familyB s, projLineCount (familyB s) (symZ p) = projLineCount (familyB s) p :=
    fun _ hp => projLineCount_symZ hp
  have hq_neg : (1, 2, -(5 * (s : ℤ) + 3)) ∈ knightD4 m2 := by
    have : -(5 * (s : ℤ) + 3) = -m2 := rfl
    rw [this]; simp [knightD4]
  have hq_pos : (1, -2, 5 * (s : ℤ) + 3) ∈ knightD4 m2 := by
    have : 5 * (s : ℤ) + 3 = m2 := rfl
    rw [this]; simp [knightD4]
  have hpos_Xa : ∀ c ∈ parityRange (9 * s + 9), 0 ≤ c →
      projLineCount (familyBE4 s) (1, 0, c) ≤ 30 * s + 31 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 9 * (s : ℤ) + 9
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ hc, rfl⟩))
        hq_neg (by simp) (familyB_isOrd hs (Or.inl ⟨rfl, Or.inl rfl⟩))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hXa_in c hc hc0 (by omega)).trans (by omega))
  have hpos_Ya : ∀ c ∈ parityRange (9 * s + 9), 0 ≤ c →
      projLineCount (familyBE4 s) (0, 1, c) ≤ 30 * s + 31 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 9 * (s : ℤ) + 9
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hc, rfl⟩)))
        hq_neg (by simp) (familyB_isOrd hs (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
      have hpB : (0, 1, c) ∈ familyB s := mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hc, rfl⟩))
      rw [← hB_symXY _ hpB, show symXY (0, 1, c) = (1, 0, c) by simp [symXY, swapXY]]
      exact (hXa_in c hc hc0 (by omega)).trans (by omega)
  have hpos_S : ∀ c ∈ parityRange (8 * s + 8), 0 ≤ c →
      projLineCount (familyBE4 s) (1, 1, c) ≤ 30 * s + 31 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 8 * (s : ℤ) + 8
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))
        hq_neg (by simp) (familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hS_in c hc hc0 (by omega)).trans (by omega))
  have hpos_N12 : ∀ c ∈ parityRange (5 * s + 5), 0 ≤ c → (1, 2, c) ∈ familyBE4 s →
      projLineCount (familyBE4 s) (1, 2, c) ≤ 30 * s + 31 := by
    intro c hc hc0 hmem
    have hc' := mem_parityRange_iff.mp hc
    have hnot_m2 : c ≠ 5 * (s : ℤ) + 3 := fun heq => (Finset.mem_sdiff.mp hmem).2 (by subst heq; simp [knightD4])
    by_cases htop : c = 5 * (s : ℤ) + 5
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))))
        hq_pos (by simp) (familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hN2_m4 c hc hc0 (by omega)).trans (by omega))
  have hpos_N21 : ∀ c ∈ parityRange (5 * s + 5), 0 ≤ c →
      projLineCount (familyBE4 s) (2, 1, c) ≤ 30 * s + 31 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 5 * (s : ℤ) + 5
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))))))
        hq_neg (by simp) (familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
    · by_cases hm2 : c = 5 * (s : ℤ) + 3
      · subst hm2
        exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))))))
          hq_pos (by simp) (familyB_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
      · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
        have hpB : (2, 1, c) ∈ familyB s :=
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))))))
        rw [← hB_symXY _ hpB, show symXY (2, 1, c) = (1, 2, c) by simp [symXY, swapXY]]
        exact (hN2_m4 c hc hc0 (by omega)).trans (by omega)
  intro p hp
  have hpB := (Finset.mem_sdiff.mp hp).1
  rcases mem_knightSet_iff.mp hpB with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
  · rcases Finset.mem_union.mp hc with hca | hce
    · by_cases h0 : 0 ≤ c
      · exact hpos_Xa c hca h0
      · rw [← hsymZ _ hp, show symZ (1, 0, c) = (1, 0, -c) by simp [symZ, negZ]]
        exact hpos_Xa (-c) (neg_mem_parityRange hca) (by omega)
    · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
      by_cases h0 : 0 ≤ c
      · exact (hXe_top c hce h0).trans (by omega)
      · rw [← hB_symZ _ hpB, show symZ (1, 0, c) = (1, 0, -c) by simp [symZ, negZ]]
        exact (hXe_top (-c) (neg_mem_parityRange hce) (by omega)).trans (by omega)
  · rcases Finset.mem_union.mp hc with hca | hce
    · by_cases h0 : 0 ≤ c
      · exact hpos_Ya c hca h0
      · rw [← hsymZ _ hp, show symZ (0, 1, c) = (0, 1, -c) by simp [symZ, negZ]]
        exact hpos_Ya (-c) (neg_mem_parityRange hca) (by omega)
    · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
      rw [← hB_symXY _ hpB, show symXY (0, 1, c) = (1, 0, c) by simp [symXY, swapXY]]
      by_cases h0 : 0 ≤ c
      · exact (hXe_top c hce h0).trans (by omega)
      · have hp1 : (1, 0, c) ∈ familyB s := mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hce, rfl⟩)
        rw [← hB_symZ _ hp1, show symZ (1, 0, c) = (1, 0, -c) by simp [symZ, negZ]]
        exact (hXe_top (-c) (neg_mem_parityRange hce) (by omega)).trans (by omega)
  · by_cases h0 : 0 ≤ c
    · exact hpos_S c hc h0
    · rw [← hsymZ _ hp, show symZ (1, 1, c) = (1, 1, -c) by simp [symZ, negZ]]
      exact hpos_S (-c) (neg_mem_parityRange hc) (by omega)
  · have hp1 := hmemY _ hp
    rw [show symY (1, -1, c) = (1, 1, c) by simp [symY, negY]] at hp1
    rw [← hsymY _ hp, show symY (1, -1, c) = (1, 1, c) by simp [symY, negY]]
    by_cases h0 : 0 ≤ c
    · exact hpos_S c hc h0
    · rw [← hsymZ _ hp1, show symZ (1, 1, c) = (1, 1, -c) by simp [symZ, negZ]]
      exact hpos_S (-c) (neg_mem_parityRange hc) (by omega)
  · by_cases h0 : 0 ≤ c
    · exact hpos_N12 c hc h0 hp
    · have hp1 := hmemZ _ hp
      rw [show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]] at hp1
      rw [← hsymZ _ hp, show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]]
      exact hpos_N12 (-c) (neg_mem_parityRange hc) (by omega) hp1
  · have hp1 := hmemY _ hp
    rw [show symY (1, -2, c) = (1, 2, c) by simp [symY, negY]] at hp1
    rw [← hsymY _ hp, show symY (1, -2, c) = (1, 2, c) by simp [symY, negY]]
    by_cases h0 : 0 ≤ c
    · exact hpos_N12 c hc h0 hp1
    · have hp2 := hmemZ _ hp1
      rw [show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]] at hp2
      rw [← hsymZ _ hp1, show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]]
      exact hpos_N12 (-c) (neg_mem_parityRange hc) (by omega) hp2
  · by_cases h0 : 0 ≤ c
    · exact hpos_N21 c hc h0
    · rw [← hsymZ _ hp, show symZ (2, 1, c) = (2, 1, -c) by simp [symZ, negZ]]
      exact hpos_N21 (-c) (neg_mem_parityRange hc) (by omega)
  · have hp1 := hmemY _ hp
    rw [show symY (2, -1, c) = (2, 1, c) by simp [symY, negY]] at hp1
    rw [← hsymY _ hp, show symY (2, -1, c) = (2, 1, c) by simp [symY, negY]]
    by_cases h0 : 0 ≤ c
    · exact hpos_N21 c hc h0
    · rw [← hsymZ _ hp1, show symZ (2, 1, c) = (2, 1, -c) by simp [symZ, negZ]]
      exact hpos_N21 (-c) (neg_mem_parityRange hc) (by omega)
  · exact (projLineCount_subset_le Finset.sdiff_subset _).trans
      ((knightSet_lineCount_origin ..).trans (by omega))

/-- **Upper Bound for New Family `A \ D_8` (`s ≥ 2`)**: every point of `familyAD8 s` lies on at
most `30s + 21 = G(60s + 45) - 1` spanned lines. -/
theorem familyAD8_lineCount_le {s : ℕ} (hs : 2 ≤ s) :
    ∀ p ∈ familyAD8 s, projLineCount (familyAD8 s) p ≤ 30 * s + 21 := by
  set m2 : ℤ := 5 * (s : ℤ) + 1
  have hDsub : knightD8 m2 ⊆ familyA s := by
    have heq : m2 = (((5 * s + 3 : ℕ) : ℤ) - 2) := by unfold m2; push_cast; ring
    rw [heq]; exact knightD8_subset_knightSet (by omega)
  have hsymZ : ∀ p ∈ familyAD8 s, projLineCount (familyAD8 s) (symZ p) = projLineCount (familyAD8 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symZ_props (9 * s + 7) (3 * s + 2) (8 * s + 6) (5 * s + 3)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD8_symZ h2 h3 hp
  have hsymY : ∀ p ∈ familyAD8 s, projLineCount (familyAD8 s) (symY p) = projLineCount (familyAD8 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symY_props (9 * s + 7) (3 * s + 2) (8 * s + 6) (5 * s + 3)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD8_symY h2 h3 hp
  have hsymXY : ∀ p ∈ familyAD8 s, projLineCount (familyAD8 s) (symXY p) = projLineCount (familyAD8 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symXY_props (9 * s + 7) (3 * s + 2) (8 * s + 6) (5 * s + 3)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD8_symXY h2 h3 hp
  obtain ⟨hXa_in, hXe_in, hS_in, hN2_in⟩ := familyA_interior_le hs
  have hdrop : ∀ {p : Pt} (hpA : p ∈ familyA s) (W : Finset Pt),
      W ⊆ knightD8 m2 → p ∉ W → (∀ q ∈ W, IsOrdinaryLine (familyA s) p q) →
      projLineCount (familyAD8 s) p + W.card ≤ projLineCount (familyA s) p := by
    intro p hpA W hWD hpW hord
    exact projLineCount_sdiff_le_sub (knightSet_proper ..) hpA hWD
      (fun q hq => Finset.mem_erase.mpr ⟨fun heq => hpW (heq ▸ hq), hDsub (hWD hq)⟩) hord
  have hpos_axis : ∀ c ∈ parityRange (9 * s + 7) ∪ parityRange (3 * s + 2), 0 ≤ c →
      projLineCount (familyAD8 s) (1, 0, c) ≤ 30 * s + 21 := by
    intro c hc hc0
    rcases Finset.mem_union.mp hc with hca | hce
    · have hca' := mem_parityRange_iff.mp hca
      by_cases htop : c = 9 * (s : ℤ) + 7
      · subst htop
        have hpA : (1, 0, 9 * (s : ℤ) + 7) ∈ familyA s :=
          mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ hca, rfl⟩)
        let W : Finset Pt := {(1, 2, -m2), (1, -2, -m2), (2, 1, -m2), (2, -1, -m2)}
        have hWc : W.card = 4 := by
          unfold W
          rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
              Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        have hd := hdrop hpA W
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl <;> simp [knightD8])
          (by simp [W])
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl
              · exact familyA_isOrd hs (Or.inl ⟨rfl, Or.inl rfl⟩)
              · exact familyA_isOrd hs (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
              · exact familyA_isOrd hs (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)
              · exact familyA_isOrd hs (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩))
        have hbd := familyA_lineCount_le s _ hpA
        omega
      · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hXa_in c hca hc0 (by omega))
    · have hce' := mem_parityRange_iff.mp hce
      by_cases htop : c = 3 * (s : ℤ) + 2
      · subst htop
        have hpA : (1, 0, 3 * (s : ℤ) + 2) ∈ familyA s :=
          mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_right _ hce, rfl⟩)
        let W : Finset Pt := {(1, 2, -m2), (1, -2, -m2), (2, 1, -m2), (2, -1, -m2)}
        have hWc : W.card = 4 := by
          unfold W
          rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
              Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        have hd := hdrop hpA W
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl <;> simp [knightD8])
          (by simp [W])
          (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl | rfl
              · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))
              · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)))
              · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))
              · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩))))
        have hbd := familyA_lineCount_le s _ hpA
        omega
      · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hXe_in c hce hc0 (by omega))
  have hall_axis : ∀ c ∈ parityRange (9 * s + 7) ∪ parityRange (3 * s + 2),
      (1, 0, c) ∈ familyAD8 s → projLineCount (familyAD8 s) (1, 0, c) ≤ 30 * s + 21 := by
    intro c hc hmem
    by_cases h0 : 0 ≤ c
    · exact hpos_axis c hc h0
    · have hnc : -c ∈ parityRange (9 * s + 7) ∪ parityRange (3 * s + 2) := by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_left _ (neg_mem_parityRange h)
        · exact Finset.mem_union_right _ (neg_mem_parityRange h)
      have hsZ : symZ (1, 0, c) = (1, 0, -c) := by simp [symZ, negZ]
      rw [← hsymZ _ hmem, hsZ]
      exact hpos_axis (-c) hnc (by omega)
  have hpos_diag : ∀ c ∈ parityRange (8 * s + 6), 0 ≤ c →
      projLineCount (familyAD8 s) (1, 1, c) ≤ 30 * s + 21 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 8 * (s : ℤ) + 6
    · subst htop
      have hpA : (1, 1, 8 * (s : ℤ) + 6) ∈ familyA s :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))
      let W : Finset Pt := {(1, 2, -m2), (1, -2, m2), (2, 1, -m2), (2, -1, -m2)}
      have hWc : W.card = 4 := by
        unfold W
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
      have hd := hdrop hpA W
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl <;> simp [knightD8])
        (by simp [W])
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))))
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)))))
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))))
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩))))))
      have hbd := familyA_lineCount_le s _ hpA
      omega
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hS_in c hc hc0 (by omega))
  have hall_diag : ∀ c ∈ parityRange (8 * s + 6),
      (1, 1, c) ∈ familyAD8 s → projLineCount (familyAD8 s) (1, 1, c) ≤ 30 * s + 21 := by
    intro c hc hmem
    by_cases h0 : 0 ≤ c
    · exact hpos_diag c hc h0
    · have hsZ : symZ (1, 1, c) = (1, 1, -c) := by simp [symZ, negZ]
      rw [← hsymZ _ hmem, hsZ]
      exact hpos_diag (-c) (neg_mem_parityRange hc) (by omega)
  have hpos_kn : ∀ c ∈ parityRange (5 * s + 3), 0 ≤ c →
      (1, 2, c) ∈ familyAD8 s → projLineCount (familyAD8 s) (1, 2, c) ≤ 30 * s + 21 := by
    intro c hc hc0 hmem
    have hc' := mem_parityRange_iff.mp hc
    have hnot_m2 : c ≠ 5 * (s : ℤ) + 1 := fun heq => (Finset.mem_sdiff.mp hmem).2 (by subst heq; simp [knightD8])
    by_cases htop : c = 5 * (s : ℤ) + 3
    · subst htop
      have hpA : (1, 2, 5 * (s : ℤ) + 3) ∈ familyA s :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))))
      let W : Finset Pt := {(1, -2, m2), (2, 1, -m2), (2, -1, -m2)}
      have hWc : W.card = 3 := by
        unfold W
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
            Finset.card_singleton]
      have hd := hdrop hpA W
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl <;> simp [knightD8])
        (by simp [W])
        (by intro q hq; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))))
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩))))))
            · exact familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)))))))
      have hbd := familyA_lineCount_le s _ hpA
      omega
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans (hN2_in c hc hc0 (by omega))
  have hall_kn : ∀ c ∈ parityRange (5 * s + 3),
      (1, 2, c) ∈ familyAD8 s → projLineCount (familyAD8 s) (1, 2, c) ≤ 30 * s + 21 := by
    intro c hc hmem
    by_cases h0 : 0 ≤ c
    · exact hpos_kn c hc h0 hmem
    · have hsZ : symZ (1, 2, c) = (1, 2, -c) := by simp [symZ, negZ]
      have hmem' : (1, 2, -c) ∈ familyAD8 s := by
        rw [← hsZ]
        refine Finset.mem_sdiff.mpr ⟨(knightSet_symZ_props ..).1 _ (Finset.mem_sdiff.mp hmem).1, ?_⟩
        intro hD
        have := knightD8_symZ _ hD
        rw [hsZ, show symZ (1, 2, -c) = (1, 2, c) by simp [symZ, negZ]] at this
        exact (Finset.mem_sdiff.mp hmem).2 this
      rw [← hsymZ _ hmem, hsZ]
      exact hpos_kn (-c) (neg_mem_parityRange hc) (by omega) hmem'
  intro p hp
  have hpA := (Finset.mem_sdiff.mp hp).1
  rcases mem_knightSet_iff.mp hpA with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
  · exact hall_axis c hc hp
  · have hsXY : symXY (0, 1, c) = (1, 0, c) := by simp [symXY, swapXY]
    have hp' : (1, 0, c) ∈ familyAD8 s := Finset.mem_sdiff.mpr
      ⟨mem_knightSet_iff.mpr (Or.inl ⟨c, hc, rfl⟩), by simp [knightD8]⟩
    rw [← hsymXY _ hp, hsXY]; exact hall_axis c hc hp'
  · exact hall_diag c hc hp
  · have hsY : symY (1, -1, c) = (1, 1, c) := by simp [symY, negY]
    have hp' : (1, 1, c) ∈ familyAD8 s := Finset.mem_sdiff.mpr
      ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))), by simp [knightD8]⟩
    rw [← hsymY _ hp, hsY]; exact hall_diag c hc hp'
  · exact hall_kn c hc hp
  · have hsY : symY (1, -2, c) = (1, 2, c) := by simp [symY, negY]
    have hp' : (1, 2, c) ∈ familyAD8 s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp).2 (by simpa [symY, negY] using knightD8_symY _ hD)
    rw [← hsymY _ hp, hsY]; exact hall_kn c hc hp'
  · have hsXY : symXY (2, 1, c) = (1, 2, c) := by simp [symXY, swapXY]
    have hp' : (1, 2, c) ∈ familyAD8 s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp).2 (by simpa [symXY, swapXY] using knightD8_symXY _ hD)
    rw [← hsymXY _ hp, hsXY]; exact hall_kn c hc hp'
  · have hsY : symY (2, -1, c) = (2, 1, c) := by simp [symY, negY]
    have hp1 : (2, 1, c) ∈ familyAD8 s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp).2 (by simpa [symY, negY] using knightD8_symY _ hD)
    have hsXY : symXY (2, 1, c) = (1, 2, c) := by simp [symXY, swapXY]
    have hp2 : (1, 2, c) ∈ familyAD8 s := by
      refine Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))), ?_⟩
      intro hD; exact (Finset.mem_sdiff.mp hp1).2 (by simpa [symXY, swapXY] using knightD8_symXY _ hD)
    rw [← hsymY _ hp, hsY, ← hsymXY _ hp1, hsXY]; exact hall_kn c hc hp2
  · exact (projLineCount_subset_le Finset.sdiff_subset _).trans
      ((knightSet_lineCount_origin ..).trans (by omega))

/-- **Upper Bound for New Family `A \ D_4` (`s ≥ 2`)**: every point of `familyAD4 s` lies on at
most `30s + 23 = G(60s + 49) - 1` spanned lines. -/
theorem familyAD4_lineCount_le {s : ℕ} (hs : 2 ≤ s) :
    ∀ p ∈ familyAD4 s, projLineCount (familyAD4 s) p ≤ 30 * s + 23 := by
  set m2 : ℤ := 5 * (s : ℤ) + 1
  have hDsub : knightD4 m2 ⊆ familyA s := by
    have heq : m2 = (((5 * s + 3 : ℕ) : ℤ) - 2) := by unfold m2; push_cast; ring
    rw [heq]; exact (knightD4_subset_knightD8 _).trans (knightD8_subset_knightSet (by omega))
  have hsymZ : ∀ p ∈ familyAD4 s, projLineCount (familyAD4 s) (symZ p) = projLineCount (familyAD4 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symZ_props (9 * s + 7) (3 * s + 2) (8 * s + 6) (5 * s + 3)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD4_symZ h2 h3 hp
  have hsymY : ∀ p ∈ familyAD4 s, projLineCount (familyAD4 s) (symY p) = projLineCount (familyAD4 s) p := by
    obtain ⟨h1, h2, h3⟩ := knightSet_symY_props (9 * s + 7) (3 * s + 2) (8 * s + 6) (5 * s + 3)
    exact fun p hp => projLineCount_sdiff_invol (knightSet_proper ..) h1 knightD4_symY h2 h3 hp
  obtain ⟨hXa_in, hXe_in, hS_in, hN2_in⟩ := familyA_interior_le hs
  have hdrop1 : ∀ {p q : Pt}, p ∈ familyA s → q ∈ knightD4 m2 → q ≠ p →
      IsOrdinaryLine (familyA s) p q → projLineCount (familyAD4 s) p ≤ 30 * s + 23 := by
    intro p q hpA hqD hqp hord
    have hsub := projLineCount_sdiff_le_sub (D := knightD4 m2) (W := {q}) (knightSet_proper ..) hpA
      (Finset.singleton_subset_iff.mpr hqD)
      (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨hqp, hDsub hqD⟩))
      (fun r hr => by rw [Finset.mem_singleton.mp hr]; exact hord)
    have hbd := familyA_lineCount_le s p hpA
    simp only [Finset.card_singleton] at hsub
    change projLineCount (familyAD4 s) p + 1 ≤ projLineCount (familyA s) p at hsub
    omega
  have hmemZ : ∀ p ∈ familyAD4 s, symZ p ∈ familyAD4 s := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨(knightSet_symZ_props ..).1 _ (Finset.mem_sdiff.mp hp).1, fun hD => ?_⟩
    have hD' := knightD4_symZ _ hD
    rw [(knightSet_symZ_props ..).2.1 _ (Finset.mem_sdiff.mp hp).1] at hD'
    exact (Finset.mem_sdiff.mp hp).2 hD'
  have hmemY : ∀ p ∈ familyAD4 s, symY p ∈ familyAD4 s := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨(knightSet_symY_props ..).1 _ (Finset.mem_sdiff.mp hp).1, fun hD => ?_⟩
    have hD' := knightD4_symY _ hD
    rw [(knightSet_symY_props ..).2.1 _ (Finset.mem_sdiff.mp hp).1] at hD'
    exact (Finset.mem_sdiff.mp hp).2 hD'
  have hA_symXY : ∀ p ∈ familyA s, projLineCount (familyA s) (symXY p) = projLineCount (familyA s) p :=
    fun _ hp => projLineCount_symXY hp
  have hq_neg : (1, 2, -(5 * (s : ℤ) + 1)) ∈ knightD4 m2 := by
    have : -(5 * (s : ℤ) + 1) = -m2 := rfl
    rw [this]; simp [knightD4]
  have hq_pos : (1, -2, 5 * (s : ℤ) + 1) ∈ knightD4 m2 := by
    have : 5 * (s : ℤ) + 1 = m2 := rfl
    rw [this]; simp [knightD4]
  have hpos_Xa : ∀ c ∈ parityRange (9 * s + 7), 0 ≤ c →
      projLineCount (familyAD4 s) (1, 0, c) ≤ 30 * s + 23 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 9 * (s : ℤ) + 7
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ hc, rfl⟩))
        hq_neg (by simp) (familyA_isOrd hs (Or.inl ⟨rfl, Or.inl rfl⟩))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hXa_in c hc hc0 (by omega)).trans (by omega))
  have hpos_Ya : ∀ c ∈ parityRange (9 * s + 7), 0 ≤ c →
      projLineCount (familyAD4 s) (0, 1, c) ≤ 30 * s + 23 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 9 * (s : ℤ) + 7
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hc, rfl⟩)))
        hq_neg (by simp) (familyA_isOrd hs (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
      have hpA : (0, 1, c) ∈ familyA s := mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hc, rfl⟩))
      rw [← hA_symXY _ hpA, show symXY (0, 1, c) = (1, 0, c) by simp [symXY, swapXY]]
      exact (hXa_in c hc hc0 (by omega)).trans (by omega)
  have hpos_Xe : ∀ c ∈ parityRange (3 * s + 2), 0 ≤ c →
      projLineCount (familyAD4 s) (1, 0, c) ≤ 30 * s + 23 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 3 * (s : ℤ) + 2
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_right _ hc, rfl⟩))
        hq_neg (by simp) (familyA_isOrd hs (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hXe_in c hc hc0 (by omega)).trans (by omega))
  have hpos_Ye : ∀ c ∈ parityRange (3 * s + 2), 0 ≤ c →
      projLineCount (familyAD4 s) (0, 1, c) ≤ 30 * s + 23 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 3 * (s : ℤ) + 2
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_right _ hc, rfl⟩)))
        hq_neg (by simp) (familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
      have hpA : (0, 1, c) ∈ familyA s := mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_right _ hc, rfl⟩))
      rw [← hA_symXY _ hpA, show symXY (0, 1, c) = (1, 0, c) by simp [symXY, swapXY]]
      exact (hXe_in c hc hc0 (by omega)).trans (by omega)
  have hpos_S : ∀ c ∈ parityRange (8 * s + 6), 0 ≤ c →
      projLineCount (familyAD4 s) (1, 1, c) ≤ 30 * s + 23 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 8 * (s : ℤ) + 6
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))
        hq_neg (by simp) (familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hS_in c hc hc0 (by omega)).trans (by omega))
  have hpos_N12 : ∀ c ∈ parityRange (5 * s + 3), 0 ≤ c → (1, 2, c) ∈ familyAD4 s →
      projLineCount (familyAD4 s) (1, 2, c) ≤ 30 * s + 23 := by
    intro c hc hc0 hmem
    have hc' := mem_parityRange_iff.mp hc
    have hnot_m2 : c ≠ 5 * (s : ℤ) + 1 := fun heq => (Finset.mem_sdiff.mp hmem).2 (by subst heq; simp [knightD4])
    by_cases htop : c = 5 * (s : ℤ) + 3
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))))
        hq_pos (by simp) (familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))))))
    · exact (projLineCount_subset_le Finset.sdiff_subset _).trans ((hN2_in c hc hc0 (by omega)).trans (by omega))
  have hpos_N21 : ∀ c ∈ parityRange (5 * s + 3), 0 ≤ c →
      projLineCount (familyAD4 s) (2, 1, c) ≤ 30 * s + 23 := by
    intro c hc hc0
    have hc' := mem_parityRange_iff.mp hc
    by_cases htop : c = 5 * (s : ℤ) + 3
    · subst htop
      exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))))))
        hq_neg (by simp) (familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
    · by_cases hm2 : c = 5 * (s : ℤ) + 1
      · subst hm2
        exact hdrop1 (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩))))))))
          hq_pos (by simp) (familyA_isOrd hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))))
      · refine (projLineCount_subset_le Finset.sdiff_subset _).trans ?_
        have hpA : (2, 1, c) ∈ familyA s :=
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hc, rfl⟩)))))))
        rw [← hA_symXY _ hpA, show symXY (2, 1, c) = (1, 2, c) by simp [symXY, swapXY]]
        exact (hN2_in c hc hc0 (by omega)).trans (by omega)
  intro p hp
  have hpA := (Finset.mem_sdiff.mp hp).1
  rcases mem_knightSet_iff.mp hpA with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
  · rcases Finset.mem_union.mp hc with hca | hce
    · by_cases h0 : 0 ≤ c
      · exact hpos_Xa c hca h0
      · rw [← hsymZ _ hp, show symZ (1, 0, c) = (1, 0, -c) by simp [symZ, negZ]]
        exact hpos_Xa (-c) (neg_mem_parityRange hca) (by omega)
    · by_cases h0 : 0 ≤ c
      · exact hpos_Xe c hce h0
      · rw [← hsymZ _ hp, show symZ (1, 0, c) = (1, 0, -c) by simp [symZ, negZ]]
        exact hpos_Xe (-c) (neg_mem_parityRange hce) (by omega)
  · rcases Finset.mem_union.mp hc with hca | hce
    · by_cases h0 : 0 ≤ c
      · exact hpos_Ya c hca h0
      · rw [← hsymZ _ hp, show symZ (0, 1, c) = (0, 1, -c) by simp [symZ, negZ]]
        exact hpos_Ya (-c) (neg_mem_parityRange hca) (by omega)
    · by_cases h0 : 0 ≤ c
      · exact hpos_Ye c hce h0
      · rw [← hsymZ _ hp, show symZ (0, 1, c) = (0, 1, -c) by simp [symZ, negZ]]
        exact hpos_Ye (-c) (neg_mem_parityRange hce) (by omega)
  · by_cases h0 : 0 ≤ c
    · exact hpos_S c hc h0
    · rw [← hsymZ _ hp, show symZ (1, 1, c) = (1, 1, -c) by simp [symZ, negZ]]
      exact hpos_S (-c) (neg_mem_parityRange hc) (by omega)
  · have hp1 := hmemY _ hp
    rw [show symY (1, -1, c) = (1, 1, c) by simp [symY, negY]] at hp1
    rw [← hsymY _ hp, show symY (1, -1, c) = (1, 1, c) by simp [symY, negY]]
    by_cases h0 : 0 ≤ c
    · exact hpos_S c hc h0
    · rw [← hsymZ _ hp1, show symZ (1, 1, c) = (1, 1, -c) by simp [symZ, negZ]]
      exact hpos_S (-c) (neg_mem_parityRange hc) (by omega)
  · by_cases h0 : 0 ≤ c
    · exact hpos_N12 c hc h0 hp
    · have hp1 := hmemZ _ hp
      rw [show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]] at hp1
      rw [← hsymZ _ hp, show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]]
      exact hpos_N12 (-c) (neg_mem_parityRange hc) (by omega) hp1
  · have hp1 := hmemY _ hp
    rw [show symY (1, -2, c) = (1, 2, c) by simp [symY, negY]] at hp1
    rw [← hsymY _ hp, show symY (1, -2, c) = (1, 2, c) by simp [symY, negY]]
    by_cases h0 : 0 ≤ c
    · exact hpos_N12 c hc h0 hp1
    · have hp2 := hmemZ _ hp1
      rw [show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]] at hp2
      rw [← hsymZ _ hp1, show symZ (1, 2, c) = (1, 2, -c) by simp [symZ, negZ]]
      exact hpos_N12 (-c) (neg_mem_parityRange hc) (by omega) hp2
  · by_cases h0 : 0 ≤ c
    · exact hpos_N21 c hc h0
    · rw [← hsymZ _ hp, show symZ (2, 1, c) = (2, 1, -c) by simp [symZ, negZ]]
      exact hpos_N21 (-c) (neg_mem_parityRange hc) (by omega)
  · have hp1 := hmemY _ hp
    rw [show symY (2, -1, c) = (2, 1, c) by simp [symY, negY]] at hp1
    rw [← hsymY _ hp, show symY (2, -1, c) = (2, 1, c) by simp [symY, negY]]
    by_cases h0 : 0 ≤ c
    · exact hpos_N21 c hc h0
    · rw [← hsymZ _ hp1, show symZ (2, 1, c) = (2, 1, -c) by simp [symZ, negZ]]
      exact hpos_N21 (-c) (neg_mem_parityRange hc) (by omega)
  · exact (projLineCount_subset_le Finset.sdiff_subset _).trans
      ((knightSet_lineCount_origin ..).trans (by omega))

/-! #### Euclidean Headlines and Combined 12-Class Mod-60 Grünbaum Refutation -/

private lemma knightSdiff_nonCollinear_erase_diag {a e b m : ℕ} {D : Finset Pt}
    (hD_ax : ∀ c : ℤ, (1, 0, c) ∉ D ∧ (0, 1, c) ∉ D) (hD_inf : (0, 0, 1) ∉ D) :
    NonCollinear ((knightSet a e b m \ D).erase (1, 1, (b : ℤ))) := by
  have ha : (a : ℤ) ∈ parityRange a := mem_parityRange_iff.mpr (by omega)
  refine ⟨(1, 0, (a : ℤ)), Finset.mem_erase.mpr ⟨by simp,
      Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩), (hD_ax _).1⟩⟩,
    (0, 1, (a : ℤ)), Finset.mem_erase.mpr ⟨by simp,
      Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)), (hD_ax _).2⟩⟩,
    (0, 0, 1), Finset.mem_erase.mpr ⟨by simp,
      Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))), hD_inf⟩⟩,
    by unfold det; ring_nf; omega⟩

/-- **Euclidean Headline for `Family C` Family C (`s ≥ 1`)**: `n = 60s + 61 = 12(5s+5) + 1`,
exact maximum spanned line count `30s + 28 = (n - 5) / 2` (deficit `5/2`, beating `G(n)` by `2`). -/
theorem deficit52_familyC_euclidean {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 61 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 28) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 28) := by
  have hnc_e := knightSdiff_nonCollinear_erase_diag (a := 9 * s + 9) (e := 3 * s + 2)
    (b := 8 * s + 8) (m := 5 * s + 5) (D := knightD8 (5 * (s : ℤ) + 3))
    (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8])
  have hnc : NonCollinear (familyC s) := by
    rcases hnc_e with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 9 : ℕ) : ℤ)) ∈ familyC s :=
    Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩), by simp [knightD8]⟩
  exact exists_euclidean_set_eq (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (familyC_card hs) hnc (familyC_lineCount_le hs) ⟨_, hp, le_of_eq (familyC_top_lineCount hs).symm⟩

/-- **Euclidean Headline for `Family E4` Family E4 (`s ≥ 1`)**: `n = 60s + 65`, `t ≤ 30s + 31 = G(n) - 1`. -/
theorem deficit52_familyBE4_euclidean {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 65 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 31 := by
  have hnc_e := knightSdiff_nonCollinear_erase_diag (a := 9 * s + 9) (e := 3 * s + 2)
    (b := 8 * s + 8) (m := 5 * s + 5) (D := knightD4 (5 * (s : ℤ) + 3))
    (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4])
  have hnc : NonCollinear (familyBE4 s) := by
    rcases hnc_e with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  exact exists_euclidean_set_le (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (familyBE4_card hs) hnc (familyBE4_lineCount_le hs)

/-- **Euclidean Headline for New Family `A \ D_8` (`s ≥ 2`)**: `n = 60s + 45`, `t ≤ 30s + 21 = G(n) - 1`. -/
theorem familyAD8_euclidean {s : ℕ} (hs : 2 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 45 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 21 := by
  have hnc_e := knightSdiff_nonCollinear_erase_diag (a := 9 * s + 7) (e := 3 * s + 2)
    (b := 8 * s + 6) (m := 5 * s + 3) (D := knightD8 (5 * (s : ℤ) + 1))
    (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8])
  have hnc : NonCollinear (familyAD8 s) := by
    rcases hnc_e with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  exact exists_euclidean_set_le (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (familyAD8_card hs) hnc (familyAD8_lineCount_le hs)

/-- **Euclidean Headline for New Family `A \ D_4` (`s ≥ 2`)**: `n = 60s + 49`, `t ≤ 30s + 23 = G(n) - 1`. -/
theorem familyAD4_euclidean {s : ℕ} (hs : 2 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 49 ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 23 := by
  have hnc_e := knightSdiff_nonCollinear_erase_diag (a := 9 * s + 7) (e := 3 * s + 2)
    (b := 8 * s + 6) (m := 5 * s + 3) (D := knightD4 (5 * (s : ℤ) + 1))
    (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4])
  have hnc : NonCollinear (familyAD4 s) := by
    rcases hnc_e with ⟨p, hp, q, hq, r, hr, hdet⟩
    exact ⟨p, Finset.mem_of_mem_erase hp, q, Finset.mem_of_mem_erase hq,
           r, Finset.mem_of_mem_erase hr, hdet⟩
  exact exists_euclidean_set_le (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (familyAD4_card hs) hnc (familyAD4_lineCount_le hs)

/-- **12-Class Mod-60 Refutation of Grünbaum's (2010) Conjecture (Target C)**:
For every `s ≥ 2`, non-collinear Euclidean configurations refute Grünbaum's conjectured
value `G(n) = 2 ⌊n / 4⌋` across **12 residue classes mod 60**:
- **6 classes by at least `2`** (`n ≡ 53, 52, 9, 8, 1, 0 (mod 60)`, covering **all 6**
  even-half mod-12 classes `m ∈ {0, 1, 4, 5, 8, 9}`);
- **6 additional classes by at least `1`** (`n ≡ 5, 4, 45, 44, 49, 48 (mod 60)`). -/
theorem grunbaum_refuted_12_mod60 {s : ℕ} (hs : 2 ≤ s) :
    -- 6 residue classes mod 60 beating G(n) by at least 2:
    ((∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 53 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 52 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 69 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 68 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 61 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 60 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2)) ∧
    -- 6 additional residue classes mod 60 beating G(n) by at least 1:
    ((∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 65 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 64 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 45 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 44 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 49 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
     (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 48 ∧ NonCollinearR2 P ∧
        ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1)) := by
  have hs1 : 1 ≤ s := by omega
  obtain ⟨hA53, hA52, hB69, hB68⟩ := deficit52_refutes_grunbaum s
  have hdel_diag : ∀ {a e b m n B : ℕ} {D : Finset Pt},
      (∀ c : ℤ, (1, 0, c) ∉ D ∧ (0, 1, c) ∉ D) → (0, 0, 1) ∉ D → (1, 1, (b : ℤ)) ∉ D →
      (knightSet a e b m \ D).card = n + 1 →
      (∀ p ∈ knightSet a e b m \ D, projLineCount (knightSet a e b m \ D) p ≤ B) →
      ∃ P : Finset (ℝ × ℝ), P.card = n ∧ NonCollinearR2 P ∧ ∀ x ∈ P, lineCountR2 P x ≤ B := by
    intro a e b m n B D hax hinf hdiag hcard hbd
    have hb : (b : ℤ) ∈ parityRange b := mem_parityRange_iff.mpr (by omega)
    have hq : (1, 1, (b : ℤ)) ∈ knightSet a e b m \ D :=
      Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), hdiag⟩
    exact exists_euclidean_erase_one (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
      hcard hq (knightSdiff_nonCollinear_erase_diag hax hinf) hbd
  refine ⟨⟨hA53, hA52, hB69, hB68, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨P, hPc, hPnc, hPbd, _⟩ := deficit52_familyC_euclidean hs1
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := hdel_diag (D := knightD8 (5 * (s : ℤ) + 3))
      (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8]) (by simp [knightD8])
      (familyC_card hs1) (familyC_lineCount_le hs1)
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := deficit52_familyBE4_euclidean hs1
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := hdel_diag (D := knightD4 (5 * (s : ℤ) + 3))
      (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4]) (by simp [knightD4])
      (familyBE4_card hs1) (familyBE4_lineCount_le hs1)
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := familyAD8_euclidean hs
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := hdel_diag (D := knightD8 (5 * (s : ℤ) + 1))
      (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8]) (by simp [knightD8])
      (familyAD8_card hs) (familyAD8_lineCount_le hs)
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := familyAD4_euclidean hs
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega
  · obtain ⟨P, hPc, hPnc, hPbd⟩ := hdel_diag (D := knightD4 (5 * (s : ℤ) + 1))
      (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4]) (by simp [knightD4])
      (familyAD4_card hs) (familyAD4_lineCount_le hs)
    refine ⟨P, hPc, hPnc, fun x hx => (hPbd x hx).trans ?_⟩
    rw [hPc]; unfold grunbaumVal; omega

end TightnessAndMod12

end StrongDirac
