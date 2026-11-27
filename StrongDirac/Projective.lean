/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# Projective Plane `ℝP²`, Spanned Line Counts, and Euclidean `ℝ²` Embedding

Provides the shared geometric foundation for the `StrongDirac` formalizations
of `R15-2-1` and `R17-2-1`:
- Integer homogeneous points `Pt := ℤ × ℤ × ℤ`, cross product `cross`,
  `3 × 3` determinant `det`, proportionality `SamePt`, and well-formed sets
  `Proper` and `NonCollinear`.
- Exact projective spanned line count `projLineCount X p` (the cardinality of
  the set of distinct projective lines `projLine p q` over `q ∈ X.erase p`).
- Label upper-bound lemma (`projLineCount_le_of_label`), witness lower-bound
  lemma (`le_projLineCount_of_witness`), and symmetry invariance
  (`projLineCount_eq_of_det_equiv`).
- Euclidean plane `ℝ²` collinearity `CollinearR2`, lines `lineR2`, exact
  spanned line count `lineCountR2 P a`, and an unconditional projective-to-Euclidean
  embedding theorem (`exists_euclidean_embedding`) sending any finite `Proper`
  projective point set into `ℝ × ℝ` while preserving cardinality,
  non-collinearity, and every point's exact spanned line count.
-/

@[expose] public section

namespace StrongDirac

/-- Integer homogeneous coordinates `(x, y, z)` representing a point in `ℝP²`. -/
abbrev Pt : Type := ℤ × ℤ × ℤ

/-- A homogeneous triple represents a projective point when it is nonzero. -/
def Nonzero (p : Pt) : Prop := p ≠ (0, 0, 0)

/-- Cross product in `ℤ³`. -/
def cross (p q : Pt) : Pt :=
  (p.2.1 * q.2.2 - p.2.2 * q.2.1,
   p.2.2 * q.1 - p.1 * q.2.2,
   p.1 * q.2.1 - p.2.1 * q.1)

/-- `3 × 3` determinant `det [p, q, r]` in `ℤ`. -/
def det (p q r : Pt) : ℤ :=
  p.1 * (q.2.1 * r.2.2 - q.2.2 * r.2.1) -
  p.2.1 * (q.1 * r.2.2 - q.2.2 * r.1) +
  p.2.2 * (q.1 * r.2.1 - q.2.1 * r.1)

/-- Two homogeneous triples represent the same projective point in `ℝP²`. -/
def SamePt (p q : Pt) : Prop :=
  ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
    a * p.1 = b * q.1 ∧ a * p.2.1 = b * q.2.1 ∧ a * p.2.2 = b * q.2.2

/-- A finite set of homogeneous triples represents `X.card` distinct points of `ℝP²`. -/
def Proper (X : Finset Pt) : Prop :=
  (∀ p ∈ X, Nonzero p) ∧ (∀ p ∈ X, ∀ q ∈ X, SamePt p q → p = q)

/-- Three points of `X` are not collinear in `ℝP²`. -/
def NonCollinear (X : Finset Pt) : Prop :=
  ∃ p ∈ X, ∃ q ∈ X, ∃ r ∈ X, det p q r ≠ 0

/-- The projective line spanned by `p` and `q`, as a set of homogeneous triples. -/
def projLine (p q : Pt) : Set Pt := {r : Pt | det p q r = 0}

/-- The finite set of distinct projective lines through `p` spanned by `X`. -/
noncomputable def spannedProjLines (X : Finset Pt) (p : Pt) : Finset (Set Pt) := by
  classical
  exact (X.erase p).image (projLine p)

/-- The exact number of distinct projective lines through `p` spanned by `X`. -/
noncomputable def projLineCount (X : Finset Pt) (p : Pt) : ℕ :=
  (spannedProjLines X p).card

/-- Predicate expressing that `p` lies on at most `N` spanned lines of `X`. -/
def AtMostLines (X : Finset Pt) (p : Pt) (N : ℕ) : Prop :=
  projLineCount X p ≤ N

/-! ### Basic Algebraic Identities for `cross`, `det`, and `SamePt` -/

lemma cross_self (p : Pt) : cross p p = (0, 0, 0) := by
  unfold cross
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring

lemma det_self_left (p q : Pt) : det p p q = 0 := by
  unfold det; ring

lemma det_self_right (p q : Pt) : det p q q = 0 := by
  unfold det; ring

lemma det_self_mid (p q : Pt) : det p q p = 0 := by
  unfold det; ring

lemma det_swap_23 (p q r : Pt) : det p r q = -det p q r := by
  unfold det; ring

lemma det_eq_dot_cross (p q r : Pt) :
    det p q r = (cross p q).1 * r.1 + (cross p q).2.1 * r.2.1 + (cross p q).2.2 * r.2.2 := by
  unfold det cross; ring

lemma cross_cross_eq_det (p q₁ q₂ : Pt) :
    cross (cross p q₁) (cross p q₂) =
      (det p q₁ q₂ * p.1, det p q₁ q₂ * p.2.1, det p q₁ q₂ * p.2.2) := by
  unfold cross det
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring

/-- Key factorization for any base point `p = (1, q0, c)`:
`det (1, q0, c) q₁ q₂` is a `2 × 2` determinant in `(b - q0 a, d - c a)`. -/
lemma det_one_left (q0 c : ℤ) (q₁ q₂ : Pt) :
    det (1, q0, c) q₁ q₂ =
      (q₁.2.1 - q0 * q₁.1) * (q₂.2.2 - c * q₂.1) -
      (q₂.2.1 - q0 * q₂.1) * (q₁.2.2 - c * q₁.1) := by
  unfold det; ring

lemma samePt_iff_cross_eq_zero {p q : Pt} (hp : Nonzero p) (hq : Nonzero q) :
    SamePt p q ↔ cross p q = (0, 0, 0) := by
  rcases p with ⟨x₁, y₁, z₁⟩
  rcases q with ⟨x₂, y₂, z₂⟩
  constructor
  · rintro ⟨a, b, ha, _hb, hx, hy, hz⟩
    unfold cross
    have h1 : a * (y₁ * z₂ - z₁ * y₂) = 0 := by
      calc a * (y₁ * z₂ - z₁ * y₂)
          = (a * y₁) * z₂ - (a * z₁) * y₂ := by ring
        _ = (b * y₂) * z₂ - (b * z₂) * y₂ := by rw [hy, hz]
        _ = 0 := by ring
    have h2 : a * (z₁ * x₂ - x₁ * z₂) = 0 := by
      calc a * (z₁ * x₂ - x₁ * z₂)
          = (a * z₁) * x₂ - (a * x₁) * z₂ := by ring
        _ = (b * z₂) * x₂ - (b * x₂) * z₂ := by rw [hz, hx]
        _ = 0 := by ring
    have h3 : a * (x₁ * y₂ - y₁ * x₂) = 0 := by
      calc a * (x₁ * y₂ - y₁ * x₂)
          = (a * x₁) * y₂ - (a * y₁) * x₂ := by ring
        _ = (b * x₂) * y₂ - (b * y₂) * x₂ := by rw [hx, hy]
        _ = 0 := by ring
    have c1 : y₁ * z₂ - z₁ * y₂ = 0 := (mul_eq_zero.mp h1).resolve_left ha
    have c2 : z₁ * x₂ - x₁ * z₂ = 0 := (mul_eq_zero.mp h2).resolve_left ha
    have c3 : x₁ * y₂ - y₁ * x₂ = 0 := (mul_eq_zero.mp h3).resolve_left ha
    exact Prod.ext c1 (Prod.ext c2 c3)
  · intro hcr
    unfold cross at hcr
    have c1 : y₁ * z₂ - z₁ * y₂ = 0 := congrArg Prod.fst hcr
    have c2 : z₁ * x₂ - x₁ * z₂ = 0 := congrArg (fun t => t.2.1) hcr
    have c3 : x₁ * y₂ - y₁ * x₂ = 0 := congrArg (fun t => t.2.2) hcr
    by_cases hx₁ : x₁ ≠ 0
    · have hx₂ : x₂ ≠ 0 := by
        intro h0
        have hy₂ : y₂ = 0 := by
          have : x₁ * y₂ = 0 := by linear_combination c3 + y₁ * h0
          exact (mul_eq_zero.mp this).resolve_left hx₁
        have hz₂ : z₂ = 0 := by
          have : x₁ * z₂ = 0 := by linear_combination -c2 + z₁ * h0
          exact (mul_eq_zero.mp this).resolve_left hx₁
        exact hq (by rw [h0, hy₂, hz₂])
      refine ⟨x₂, x₁, hx₂, hx₁, ?_, ?_, ?_⟩
      · ring
      · linear_combination -c3
      · linear_combination c2
    · push Not at hx₁
      by_cases hy₁ : y₁ ≠ 0
      · have hy₂ : y₂ ≠ 0 := by
          intro h0
          have hx₂ : x₂ = 0 := by
            have : y₁ * x₂ = 0 := by linear_combination -c3 + x₁ * h0
            exact (mul_eq_zero.mp this).resolve_left hy₁
          have hz₂ : z₂ = 0 := by
            have : y₁ * z₂ = 0 := by linear_combination c1 + z₁ * h0
            exact (mul_eq_zero.mp this).resolve_left hy₁
          exact hq (by rw [hx₂, h0, hz₂])
        refine ⟨y₂, y₁, hy₂, hy₁, ?_, ?_, ?_⟩
        · linear_combination c3
        · ring
        · linear_combination -c1
      · push Not at hy₁
        have hz₁ : z₁ ≠ 0 := by
          intro h0; exact hp (by rw [hx₁, hy₁, h0])
        have hz₂ : z₂ ≠ 0 := by
          intro h0
          have hx₂ : x₂ = 0 := by
            have : z₁ * x₂ = 0 := by linear_combination c2 + x₁ * h0
            exact (mul_eq_zero.mp this).resolve_left hz₁
          have hy₂ : y₂ = 0 := by
            have : z₁ * y₂ = 0 := by linear_combination -c1 + y₁ * h0
            exact (mul_eq_zero.mp this).resolve_left hz₁
          exact hq (by rw [hx₂, hy₂, h0])
        refine ⟨z₂, z₁, hz₂, hz₁, ?_, ?_, ?_⟩
        · linear_combination -c2
        · linear_combination c1
        · ring

lemma not_samePt_of_cross_ne_zero {p q : Pt} (h : cross p q ≠ (0, 0, 0)) : ¬ SamePt p q := by
  intro hs
  by_cases hp : Nonzero p
  · by_cases hq : Nonzero q
    · exact h ((samePt_iff_cross_eq_zero hp hq).mp hs)
    · unfold Nonzero at hq; push Not at hq
      rw [hq] at h; unfold cross at h; simp at h
  · unfold Nonzero at hp; push Not at hp
    rw [hp] at h; unfold cross at h; simp at h

lemma projLine_eq_iff_det_eq_zero {p q₁ q₂ : Pt} (hp : Nonzero p)
    (hq₁ : Nonzero q₁) (hq₂ : Nonzero q₂)
    (h1 : ¬ SamePt p q₁) (h2 : ¬ SamePt p q₂) :
    projLine p q₁ = projLine p q₂ ↔ det p q₁ q₂ = 0 := by
  constructor
  · intro heq
    have hmem : q₂ ∈ projLine p q₂ := det_self_right p q₂
    rw [← heq] at hmem
    exact hmem
  · intro hdet
    have hu : Nonzero (cross p q₁) := fun h0 => h1 ((samePt_iff_cross_eq_zero hp hq₁).mpr h0)
    have hv : Nonzero (cross p q₂) := fun h0 => h2 ((samePt_iff_cross_eq_zero hp hq₂).mpr h0)
    have hcr : cross (cross p q₁) (cross p q₂) = (0, 0, 0) := by
      rw [cross_cross_eq_det, hdet]; simp
    have hsame : SamePt (cross p q₁) (cross p q₂) :=
      (samePt_iff_cross_eq_zero hu hv).mpr hcr
    rcases hsame with ⟨a, b, ha, hb, hx, hy, hz⟩
    ext r
    simp only [projLine, Set.mem_ofPred_eq, det_eq_dot_cross]
    constructor
    · intro hr
      have hscaled : b * ((cross p q₂).1 * r.1 + (cross p q₂).2.1 * r.2.1 +
          (cross p q₂).2.2 * r.2.2) = 0 := by
        calc b * ((cross p q₂).1 * r.1 + (cross p q₂).2.1 * r.2.1 + (cross p q₂).2.2 * r.2.2)
            = (b * (cross p q₂).1) * r.1 + (b * (cross p q₂).2.1) * r.2.1 +
              (b * (cross p q₂).2.2) * r.2.2 := by ring
          _ = (a * (cross p q₁).1) * r.1 + (a * (cross p q₁).2.1) * r.2.1 +
              (a * (cross p q₁).2.2) * r.2.2 := by rw [← hx, ← hy, ← hz]
          _ = a * ((cross p q₁).1 * r.1 + (cross p q₁).2.1 * r.2.1 +
              (cross p q₁).2.2 * r.2.2) := by ring
          _ = a * 0 := by rw [hr]
          _ = 0 := by ring
      exact (mul_eq_zero.mp hscaled).resolve_left hb
    · intro hr
      have hscaled : a * ((cross p q₁).1 * r.1 + (cross p q₁).2.1 * r.2.1 +
          (cross p q₁).2.2 * r.2.2) = 0 := by
        calc a * ((cross p q₁).1 * r.1 + (cross p q₁).2.1 * r.2.1 + (cross p q₁).2.2 * r.2.2)
            = (a * (cross p q₁).1) * r.1 + (a * (cross p q₁).2.1) * r.2.1 +
              (a * (cross p q₁).2.2) * r.2.2 := by ring
          _ = (b * (cross p q₂).1) * r.1 + (b * (cross p q₂).2.1) * r.2.1 +
              (b * (cross p q₂).2.2) * r.2.2 := by rw [hx, hy, hz]
          _ = b * ((cross p q₂).1 * r.1 + (cross p q₂).2.1 * r.2.1 +
              (cross p q₂).2.2 * r.2.2) := by ring
          _ = b * 0 := by rw [hr]
          _ = 0 := by ring
      exact (mul_eq_zero.mp hscaled).resolve_left ha

/-! ### Counting Lemmas and Symmetry Invariance -/

/-- Coloring/label upper bound on `projLineCount`: if every `q ∈ X.erase p` maps
into a finite label set `L` of cardinality `≤ N`, and equal labels force
`det p q₁ q₂ = 0`, then `projLineCount X p ≤ N`. -/
theorem projLineCount_le_of_label {β : Type*} [DecidableEq β]
    {X : Finset Pt} {p : Pt} {N : ℕ}
    (hX : Proper X) (hp : p ∈ X)
    (label : Pt → β) (L : Finset β) (hL : L.card ≤ N)
    (hmem : ∀ q ∈ X.erase p, label q ∈ L)
    (hcoll : ∀ q₁ ∈ X.erase p, ∀ q₂ ∈ X.erase p, label q₁ = label q₂ → det p q₁ q₂ = 0) :
    projLineCount X p ≤ N := by
  classical
  have hcard : (spannedProjLines X p).card ≤ L.card := by
    let f : Set Pt → β := fun l =>
      if h : ∃ q ∈ X.erase p, projLine p q = l then label (Classical.choose h) else label p
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro l hl
      rw [Finset.mem_coe, spannedProjLines, Finset.mem_image] at hl
      have hf : f l = label (Classical.choose hl) := by
        dsimp only [f]; exact dite_eq_left_of_eq_true (eq_true hl)
      rw [hf, Finset.mem_coe]
      exact hmem _ (Classical.choose_spec hl).1
    · intro l₁ hl₁ l₂ hl₂ heq
      rw [Finset.mem_coe, spannedProjLines, Finset.mem_image] at hl₁ hl₂
      have hf₁ : f l₁ = label (Classical.choose hl₁) := by
        dsimp only [f]; exact dite_eq_left_of_eq_true (eq_true hl₁)
      have hf₂ : f l₂ = label (Classical.choose hl₂) := by
        dsimp only [f]; exact dite_eq_left_of_eq_true (eq_true hl₂)
      rw [hf₁, hf₂] at heq
      set q₁ := Classical.choose hl₁
      set q₂ := Classical.choose hl₂
      have hq₁ : q₁ ∈ X.erase p ∧ projLine p q₁ = l₁ := Classical.choose_spec hl₁
      have hq₂ : q₂ ∈ X.erase p ∧ projLine p q₂ = l₂ := Classical.choose_spec hl₂
      have hdet : det p q₁ q₂ = 0 := hcoll q₁ hq₁.1 q₂ hq₂.1 heq
      have hne₁ : q₁ ≠ p := (Finset.mem_erase.mp hq₁.1).1
      have hne₂ : q₂ ≠ p := (Finset.mem_erase.mp hq₂.1).1
      have hmem₁ : q₁ ∈ X := Finset.mem_of_mem_erase hq₁.1
      have hmem₂ : q₂ ∈ X := Finset.mem_of_mem_erase hq₂.1
      have hns₁ : ¬ SamePt p q₁ := fun hs => hne₁ (hX.2 p hp q₁ hmem₁ hs).symm
      have hns₂ : ¬ SamePt p q₂ := fun hs => hne₂ (hX.2 p hp q₂ hmem₂ hs).symm
      rw [← hq₁.2, ← hq₂.2]
      exact (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 q₁ hmem₁) (hX.1 q₂ hmem₂)
        hns₁ hns₂).mpr hdet
  exact hcard.trans hL

/-- Witness lower bound on `projLineCount`: any subset `W ⊆ X.erase p` whose
elements have pairwise nonzero determinant with `p` contributes at least
`W.card` distinct spanned lines through `p`. -/
theorem le_projLineCount_of_witness
    {X : Finset Pt} {p : Pt}
    (hX : Proper X) (hp : p ∈ X)
    (W : Finset Pt) (hW : W ⊆ X.erase p)
    (hsep : ∀ q₁ ∈ W, ∀ q₂ ∈ W, q₁ ≠ q₂ → det p q₁ q₂ ≠ 0) :
    W.card ≤ projLineCount X p := by
  classical
  refine Finset.card_le_card_of_injOn (projLine p) ?_ ?_
  · intro q hq
    simp only [spannedProjLines, Finset.mem_coe, Finset.mem_image]
    exact ⟨q, hW hq, rfl⟩
  · intro q₁ hq₁ q₂ hq₂ heq
    by_contra hne
    have hm₁ := hW hq₁
    have hm₂ := hW hq₂
    have hns₁ : ¬ SamePt p q₁ :=
      fun hs => (Finset.mem_erase.mp hm₁).1 (hX.2 p hp q₁ (Finset.mem_of_mem_erase hm₁) hs).symm
    have hns₂ : ¬ SamePt p q₂ :=
      fun hs => (Finset.mem_erase.mp hm₂).1 (hX.2 p hp q₂ (Finset.mem_of_mem_erase hm₂) hs).symm
    have hdet : det p q₁ q₂ = 0 :=
      (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 q₁ (Finset.mem_of_mem_erase hm₁))
        (hX.1 q₂ (Finset.mem_of_mem_erase hm₂)) hns₁ hns₂).mp heq
    exact hsep q₁ hq₁ q₂ hq₂ hne hdet

/-- Symmetry invariance: any bijection `T : X → X` preserving zero determinants
preserves `projLineCount`. -/
theorem projLineCount_eq_of_det_equiv
    {X : Finset Pt} {p : Pt}
    (hX : Proper X) (hp : p ∈ X)
    (T Tinv : Pt → Pt)
    (hT_mem : ∀ q ∈ X, T q ∈ X)
    (hTinv_mem : ∀ q ∈ X, Tinv q ∈ X)
    (hTinv_T : ∀ q ∈ X, Tinv (T q) = q)
    (hT_Tinv : ∀ q ∈ X, T (Tinv q) = q)
    (hdet : ∀ a b c : Pt, det (T a) (T b) (T c) = 0 ↔ det a b c = 0) :
    projLineCount X (T p) = projLineCount X p := by
  classical
  have hle₁ : projLineCount X p ≤ projLineCount X (T p) := by
    refine projLineCount_le_of_label hX hp (fun q => projLine (T p) (T q))
      (spannedProjLines X (T p)) le_rfl ?_ ?_
    · intro q hq
      have hqm : q ∈ X := Finset.mem_of_mem_erase hq
      have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
      have hTne : T q ≠ T p := fun h => hqne (by rw [← hTinv_T q hqm, ← hTinv_T p hp, h])
      simp only [spannedProjLines, Finset.mem_image]
      exact ⟨T q, Finset.mem_erase.mpr ⟨hTne, hT_mem q hqm⟩, rfl⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      have hm₁ : q₁ ∈ X := Finset.mem_of_mem_erase hq₁
      have hm₂ : q₂ ∈ X := Finset.mem_of_mem_erase hq₂
      have hTne₁ : T q₁ ≠ T p :=
        fun h => (Finset.mem_erase.mp hq₁).1 (by rw [← hTinv_T q₁ hm₁, ← hTinv_T p hp, h])
      have hTne₂ : T q₂ ≠ T p :=
        fun h => (Finset.mem_erase.mp hq₂).1 (by rw [← hTinv_T q₂ hm₂, ← hTinv_T p hp, h])
      have hns₁ : ¬ SamePt (T p) (T q₁) :=
        fun hs => hTne₁ (hX.2 (T p) (hT_mem p hp) (T q₁) (hT_mem q₁ hm₁) hs).symm
      have hns₂ : ¬ SamePt (T p) (T q₂) :=
        fun hs => hTne₂ (hX.2 (T p) (hT_mem p hp) (T q₂) (hT_mem q₂ hm₂) hs).symm
      have hdT : det (T p) (T q₁) (T q₂) = 0 :=
        (projLine_eq_iff_det_eq_zero (hX.1 (T p) (hT_mem p hp)) (hX.1 (T q₁) (hT_mem q₁ hm₁))
          (hX.1 (T q₂) (hT_mem q₂ hm₂)) hns₁ hns₂).mp heq
      exact (hdet p q₁ q₂).mp hdT
  have hle₂ : projLineCount X (T p) ≤ projLineCount X p := by
    refine projLineCount_le_of_label hX (hT_mem p hp) (fun q => projLine p (Tinv q))
      (spannedProjLines X p) le_rfl ?_ ?_
    · intro q hq
      have hqm : q ∈ X := Finset.mem_of_mem_erase hq
      have hqne : q ≠ T p := (Finset.mem_erase.mp hq).1
      have hIne : Tinv q ≠ p := fun h => hqne (by rw [← hT_Tinv q hqm, h])
      simp only [spannedProjLines, Finset.mem_image]
      exact ⟨Tinv q, Finset.mem_erase.mpr ⟨hIne, hTinv_mem q hqm⟩, rfl⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      have hm₁ : q₁ ∈ X := Finset.mem_of_mem_erase hq₁
      have hm₂ : q₂ ∈ X := Finset.mem_of_mem_erase hq₂
      have hIne₁ : Tinv q₁ ≠ p :=
        fun h => (Finset.mem_erase.mp hq₁).1 (by rw [← hT_Tinv q₁ hm₁, h])
      have hIne₂ : Tinv q₂ ≠ p :=
        fun h => (Finset.mem_erase.mp hq₂).1 (by rw [← hT_Tinv q₂ hm₂, h])
      have hns₁ : ¬ SamePt p (Tinv q₁) :=
        fun hs => hIne₁ (hX.2 p hp (Tinv q₁) (hTinv_mem q₁ hm₁) hs).symm
      have hns₂ : ¬ SamePt p (Tinv q₂) :=
        fun hs => hIne₂ (hX.2 p hp (Tinv q₂) (hTinv_mem q₂ hm₂) hs).symm
      have hdI : det p (Tinv q₁) (Tinv q₂) = 0 :=
        (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 (Tinv q₁) (hTinv_mem q₁ hm₁))
          (hX.1 (Tinv q₂) (hTinv_mem q₂ hm₂)) hns₁ hns₂).mp heq
      have hdT := (hdet p (Tinv q₁) (Tinv q₂)).mpr hdI
      rwa [hT_Tinv q₁ hm₁, hT_Tinv q₂ hm₂] at hdT
  exact le_antisymm hle₂ hle₁

/-! ### Standard Coordinate Symmetries -/

/-- Swap the first two homogeneous coordinates `(x, y, z) ↦ (y, x, z)`. -/
def swapXY (p : Pt) : Pt := (p.2.1, p.1, p.2.2)

/-- Negate the second homogeneous coordinate `(x, y, z) ↦ (x, -y, z)`. -/
def negY (p : Pt) : Pt := (p.1, -p.2.1, p.2.2)

/-- Negate the third homogeneous coordinate `(x, y, z) ↦ (x, y, -z)`. -/
def negZ (p : Pt) : Pt := (p.1, p.2.1, -p.2.2)

lemma det_swapXY (a b c : Pt) : det (swapXY a) (swapXY b) (swapXY c) = -det a b c := by
  unfold det swapXY; ring

lemma det_negY (a b c : Pt) : det (negY a) (negY b) (negY c) = -det a b c := by
  unfold det negY; ring

lemma det_negZ (a b c : Pt) : det (negZ a) (negZ b) (negZ c) = -det a b c := by
  unfold det negZ; ring

lemma swapXY_involutive (p : Pt) : swapXY (swapXY p) = p := by
  rcases p with ⟨x, y, z⟩; rfl

lemma negY_involutive (p : Pt) : negY (negY p) = p := by
  rcases p with ⟨x, y, z⟩; simp [negY]

lemma negZ_involutive (p : Pt) : negZ (negZ p) = p := by
  rcases p with ⟨x, y, z⟩; simp [negZ]

/-! ### Euclidean Plane `ℝ²` and Projective-to-Euclidean Embedding -/

/-- Three points in `ℝ²` are collinear iff their `2 × 2` signed area vanishes. -/
def CollinearR2 (a b c : ℝ × ℝ) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

/-- A finite set of points in `ℝ²` is not all collinear. -/
def NonCollinearR2 (P : Finset (ℝ × ℝ)) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ CollinearR2 a b c

/-- The Euclidean line through `a` and `b` in `ℝ²`. -/
def lineR2 (a b : ℝ × ℝ) : Set (ℝ × ℝ) := {r : ℝ × ℝ | CollinearR2 a b r}

/-- The finite set of distinct Euclidean lines through `a` spanned by `P`. -/
noncomputable def spannedLinesR2 (P : Finset (ℝ × ℝ)) (a : ℝ × ℝ) : Finset (Set (ℝ × ℝ)) := by
  classical
  exact (P.erase a).image (lineR2 a)

/-- The exact number of distinct Euclidean lines through `a` spanned by `P`. -/
noncomputable def lineCountR2 (P : Finset (ℝ × ℝ)) (a : ℝ × ℝ) : ℕ :=
  (spannedLinesR2 P a).card

lemma collinearR2_self_right (a b : ℝ × ℝ) : CollinearR2 a b b := by
  unfold CollinearR2; ring

lemma lineR2_eq_iff_collinearR2 {a b c : ℝ × ℝ} (hab : a ≠ b) (hac : a ≠ c) :
    lineR2 a b = lineR2 a c ↔ CollinearR2 a b c := by
  constructor
  · intro heq
    have hmem : c ∈ lineR2 a c := collinearR2_self_right a c
    rw [← heq] at hmem
    exact hmem
  · intro hcol
    unfold CollinearR2 at hcol
    ext r
    simp only [lineR2, Set.mem_ofPred_eq, CollinearR2]
    have hba : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hab
      exact Prod.ext (by linarith) (by linarith)
    have hca : c.1 - a.1 ≠ 0 ∨ c.2 - a.2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hac
      exact Prod.ext (by linarith) (by linarith)
    constructor
    · intro hr
      rcases hba with hbx | hby
      · have hmul : (b.1 - a.1) * ((c.1 - a.1) * (r.2 - a.2) - (c.2 - a.2) * (r.1 - a.1)) = 0 := by
          linear_combination (c.1 - a.1) * hr - (r.1 - a.1) * hcol
        exact (mul_eq_zero.mp hmul).resolve_left hbx
      · have hmul : (b.2 - a.2) * ((c.1 - a.1) * (r.2 - a.2) - (c.2 - a.2) * (r.1 - a.1)) = 0 := by
          linear_combination (c.2 - a.2) * hr - (r.2 - a.2) * hcol
        exact (mul_eq_zero.mp hmul).resolve_left hby
    · intro hr
      rcases hca with hcx | hcy
      · have hmul : (c.1 - a.1) * ((b.1 - a.1) * (r.2 - a.2) - (b.2 - a.2) * (r.1 - a.1)) = 0 := by
          linear_combination (b.1 - a.1) * hr + (r.1 - a.1) * hcol
        exact (mul_eq_zero.mp hmul).resolve_left hcx
      · have hmul : (c.2 - a.2) * ((b.1 - a.1) * (r.2 - a.2) - (b.2 - a.2) * (r.1 - a.1)) = 0 := by
          linear_combination (b.2 - a.2) * hr + (r.2 - a.2) * hcol
        exact (mul_eq_zero.mp hmul).resolve_left hcy

/-- Affine-chart denominator `x + t y + t² z` for the unimodular projective chart
`M(t) = [[0, 1, 0], [0, 0, 1], [1, t, t²]]` (`det M(t) = 1`). -/
def denom (t : ℝ) (p : Pt) : ℝ :=
  (p.1 : ℝ) + t * (p.2.1 : ℝ) + t ^ 2 * (p.2.2 : ℝ)

/-- Explicit projective-to-Euclidean chart `φ_t(x, y, z) = (y / D, z / D)`. -/
noncomputable def projToR2 (t : ℝ) (p : Pt) : ℝ × ℝ :=
  ((p.2.1 : ℝ) / denom t p, (p.2.2 : ℝ) / denom t p)

/-- Exact determinant scaling identity for `projToR2 t`:
the Euclidean `2 × 2` signed area equals `det p q r / (D_p D_q D_r)`. -/
lemma area_projToR2_mul_denoms (t : ℝ) {p q r : Pt}
    (hp : denom t p ≠ 0) (hq : denom t q ≠ 0) (hr : denom t r ≠ 0) :
    ((projToR2 t q).1 - (projToR2 t p).1) * ((projToR2 t r).2 - (projToR2 t p).2) -
    ((projToR2 t q).2 - (projToR2 t p).2) * ((projToR2 t r).1 - (projToR2 t p).1) =
    (det p q r : ℝ) / (denom t p * denom t q * denom t r) := by
  have hmul : denom t p * denom t q * denom t r ≠ 0 := mul_ne_zero (mul_ne_zero hp hq) hr
  rw [eq_div_iff hmul]
  have hq1 : (projToR2 t q).1 * denom t q = (q.2.1 : ℝ) := div_mul_cancel₀ _ hq
  have hq2 : (projToR2 t q).2 * denom t q = (q.2.2 : ℝ) := div_mul_cancel₀ _ hq
  have hp1 : (projToR2 t p).1 * denom t p = (p.2.1 : ℝ) := div_mul_cancel₀ _ hp
  have hp2 : (projToR2 t p).2 * denom t p = (p.2.2 : ℝ) := div_mul_cancel₀ _ hp
  have hr1 : (projToR2 t r).1 * denom t r = (r.2.1 : ℝ) := div_mul_cancel₀ _ hr
  have hr2 : (projToR2 t r).2 * denom t r = (r.2.2 : ℝ) := div_mul_cancel₀ _ hr
  have h1 : (((projToR2 t q).1 - (projToR2 t p).1) * ((projToR2 t r).2 - (projToR2 t p).2) -
      ((projToR2 t q).2 - (projToR2 t p).2) * ((projToR2 t r).1 - (projToR2 t p).1)) *
      (denom t p * denom t q * denom t r) =
      denom t p * ((q.2.1 : ℝ) * (r.2.2 : ℝ) - (q.2.2 : ℝ) * (r.2.1 : ℝ)) -
      denom t q * ((p.2.1 : ℝ) * (r.2.2 : ℝ) - (p.2.2 : ℝ) * (r.2.1 : ℝ)) +
      denom t r * ((p.2.1 : ℝ) * (q.2.2 : ℝ) - (p.2.2 : ℝ) * (q.2.1 : ℝ)) := by
    calc (((projToR2 t q).1 - (projToR2 t p).1) * ((projToR2 t r).2 - (projToR2 t p).2) -
          ((projToR2 t q).2 - (projToR2 t p).2) * ((projToR2 t r).1 - (projToR2 t p).1)) *
          (denom t p * denom t q * denom t r)
        = denom t p * (((projToR2 t q).1 * denom t q) * ((projToR2 t r).2 * denom t r) -
                       ((projToR2 t q).2 * denom t q) * ((projToR2 t r).1 * denom t r)) -
          denom t q * (((projToR2 t p).1 * denom t p) * ((projToR2 t r).2 * denom t r) -
                       ((projToR2 t p).2 * denom t p) * ((projToR2 t r).1 * denom t r)) +
          denom t r * (((projToR2 t p).1 * denom t p) * ((projToR2 t q).2 * denom t q) -
                       ((projToR2 t p).2 * denom t p) * ((projToR2 t q).1 * denom t q)) := by ring
      _ = _ := by rw [hp1, hp2, hq1, hq2, hr1, hr2]
  rw [h1]
  unfold denom det
  push_cast
  ring

lemma collinearR2_projToR2_iff (t : ℝ) {p q r : Pt}
    (hp : denom t p ≠ 0) (hq : denom t q ≠ 0) (hr : denom t r ≠ 0) :
    CollinearR2 (projToR2 t p) (projToR2 t q) (projToR2 t r) ↔ det p q r = 0 := by
  unfold CollinearR2
  rw [area_projToR2_mul_denoms t hp hq hr]
  have hden : denom t p * denom t q * denom t r ≠ 0 := mul_ne_zero (mul_ne_zero hp hq) hr
  rw [div_eq_zero_iff]
  simp only [hden, or_false, Int.cast_eq_zero]

lemma projToR2_injOn (t : ℝ) {X : Finset Pt} (hX : Proper X)
    (hden : ∀ p ∈ X, denom t p ≠ 0) :
    Set.InjOn (projToR2 t) X := by
  intro p hp q hq heq
  have hdp : denom t p ≠ 0 := hden p hp
  have hdq : denom t q ≠ 0 := hden q hq
  have h1 : (p.2.1 : ℝ) / denom t p = (q.2.1 : ℝ) / denom t q := congrArg Prod.fst heq
  have h2 : (p.2.2 : ℝ) / denom t p = (q.2.2 : ℝ) / denom t q := congrArg Prod.snd heq
  have hy : (p.2.1 : ℝ) * denom t q = (q.2.1 : ℝ) * denom t p := (div_eq_div_iff hdp hdq).mp h1
  have hz : (p.2.2 : ℝ) * denom t q = (q.2.2 : ℝ) * denom t p := (div_eq_div_iff hdp hdq).mp h2
  have hx : (p.1 : ℝ) * denom t q = (q.1 : ℝ) * denom t p := by
    have hp_eq : (p.1 : ℝ) = denom t p - t * (p.2.1 : ℝ) - t ^ 2 * (p.2.2 : ℝ) := by
      unfold denom; ring
    have hq_eq : (q.1 : ℝ) = denom t q - t * (q.2.1 : ℝ) - t ^ 2 * (q.2.2 : ℝ) := by
      unfold denom; ring
    calc (p.1 : ℝ) * denom t q
        = denom t p * denom t q - t * ((p.2.1 : ℝ) * denom t q) -
          t ^ 2 * ((p.2.2 : ℝ) * denom t q) := by rw [hp_eq]; ring
      _ = denom t p * denom t q - t * ((q.2.1 : ℝ) * denom t p) -
          t ^ 2 * ((q.2.2 : ℝ) * denom t p) := by rw [hy, hz]
      _ = (q.1 : ℝ) * denom t p := by rw [hq_eq]; ring
  have hc1 : p.2.1 * q.2.2 - p.2.2 * q.2.1 = 0 := by
    have hr : ((p.2.1 * q.2.2 - p.2.2 * q.2.1 : ℤ) : ℝ) * denom t p = 0 := by
      push_cast
      calc ((p.2.1 : ℝ) * (q.2.2 : ℝ) - (p.2.2 : ℝ) * (q.2.1 : ℝ)) * denom t p
          = (p.2.1 : ℝ) * ((q.2.2 : ℝ) * denom t p) -
            (p.2.2 : ℝ) * ((q.2.1 : ℝ) * denom t p) := by ring
        _ = (p.2.1 : ℝ) * ((p.2.2 : ℝ) * denom t q) -
            (p.2.2 : ℝ) * ((p.2.1 : ℝ) * denom t q) := by rw [← hz, ← hy]
        _ = 0 := by ring
    exact Int.cast_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hdp)
  have hc2 : p.2.2 * q.1 - p.1 * q.2.2 = 0 := by
    have hr : ((p.2.2 * q.1 - p.1 * q.2.2 : ℤ) : ℝ) * denom t p = 0 := by
      push_cast
      calc ((p.2.2 : ℝ) * (q.1 : ℝ) - (p.1 : ℝ) * (q.2.2 : ℝ)) * denom t p
          = (p.2.2 : ℝ) * ((q.1 : ℝ) * denom t p) -
            (p.1 : ℝ) * ((q.2.2 : ℝ) * denom t p) := by ring
        _ = (p.2.2 : ℝ) * ((p.1 : ℝ) * denom t q) -
            (p.1 : ℝ) * ((p.2.2 : ℝ) * denom t q) := by rw [← hx, ← hz]
        _ = 0 := by ring
    exact Int.cast_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hdp)
  have hc3 : p.1 * q.2.1 - p.2.1 * q.1 = 0 := by
    have hr : ((p.1 * q.2.1 - p.2.1 * q.1 : ℤ) : ℝ) * denom t p = 0 := by
      push_cast
      calc ((p.1 : ℝ) * (q.2.1 : ℝ) - (p.2.1 : ℝ) * (q.1 : ℝ)) * denom t p
          = (p.1 : ℝ) * ((q.2.1 : ℝ) * denom t p) -
            (p.2.1 : ℝ) * ((q.1 : ℝ) * denom t p) := by ring
        _ = (p.1 : ℝ) * ((p.2.1 : ℝ) * denom t q) -
            (p.2.1 : ℝ) * ((p.1 : ℝ) * denom t q) := by rw [← hy, ← hx]
        _ = 0 := by ring
    exact Int.cast_eq_zero.mp ((mul_eq_zero.mp hr).resolve_right hdp)
  have hcr : cross p q = (0, 0, 0) := Prod.ext hc1 (Prod.ext hc2 hc3)
  exact hX.2 p hp q hq ((samePt_iff_cross_eq_zero (hX.1 p hp) (hX.1 q hq)).mpr hcr)

/-- A nonzero quadratic `x + t y + t² z` has at most two real roots. -/
lemma quadratic_roots_card_le_two {p : Pt} (hp : Nonzero p) (S : Finset ℕ) :
    (S.filter (fun k : ℕ => denom (k : ℝ) p = 0)).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hgt
  have r1 : (p.1 : ℝ) + (k₁ : ℝ) * (p.2.1 : ℝ) + (k₁ : ℝ) ^ 2 * (p.2.2 : ℝ) = 0 :=
    (Finset.mem_filter.mp hk₁).2
  have r2 : (p.1 : ℝ) + (k₂ : ℝ) * (p.2.1 : ℝ) + (k₂ : ℝ) ^ 2 * (p.2.2 : ℝ) = 0 :=
    (Finset.mem_filter.mp hk₂).2
  have r3 : (p.1 : ℝ) + (k₃ : ℝ) * (p.2.1 : ℝ) + (k₃ : ℝ) ^ 2 * (p.2.2 : ℝ) = 0 :=
    (Finset.mem_filter.mp hk₃).2
  have d12 : (k₂ : ℝ) - (k₁ : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h12.symm)
  have d13 : (k₃ : ℝ) - (k₁ : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h13.symm)
  have d23 : (k₃ : ℝ) - (k₂ : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h23.symm)
  have e12 : (p.2.1 : ℝ) + ((k₂ : ℝ) + (k₁ : ℝ)) * (p.2.2 : ℝ) = 0 := by
    have hmul : ((k₂ : ℝ) - (k₁ : ℝ)) * ((p.2.1 : ℝ) + ((k₂ : ℝ) + (k₁ : ℝ)) * (p.2.2 : ℝ)) = 0 := by
      linear_combination r2 - r1
    exact (mul_eq_zero.mp hmul).resolve_left d12
  have e13 : (p.2.1 : ℝ) + ((k₃ : ℝ) + (k₁ : ℝ)) * (p.2.2 : ℝ) = 0 := by
    have hmul : ((k₃ : ℝ) - (k₁ : ℝ)) * ((p.2.1 : ℝ) + ((k₃ : ℝ) + (k₁ : ℝ)) * (p.2.2 : ℝ)) = 0 := by
      linear_combination r3 - r1
    exact (mul_eq_zero.mp hmul).resolve_left d13
  have hzR : (p.2.2 : ℝ) = 0 := by
    have hmul : ((k₃ : ℝ) - (k₂ : ℝ)) * (p.2.2 : ℝ) = 0 := by
      linear_combination e13 - e12
    exact (mul_eq_zero.mp hmul).resolve_left d23
  have hyR : (p.2.1 : ℝ) = 0 := by linear_combination e12 - ((k₂ : ℝ) + (k₁ : ℝ)) * hzR
  have hxR : (p.1 : ℝ) = 0 := by linear_combination r1 - (k₁ : ℝ) * hyR - (k₁ : ℝ) ^ 2 * hzR
  have hx : p.1 = 0 := Int.cast_eq_zero.mp hxR
  have hy : p.2.1 = 0 := Int.cast_eq_zero.mp hyR
  have hz : p.2.2 = 0 := Int.cast_eq_zero.mp hzR
  exact hp (Prod.ext hx (Prod.ext hy hz))

/-- Pigeonhole existence of a natural-number parameter `k` whose affine chart
avoids every point of `X`. -/
theorem exists_good_param (X : Finset Pt) (hX : ∀ p ∈ X, Nonzero p) :
    ∃ t : ℝ, ∀ p ∈ X, denom t p ≠ 0 := by
  classical
  let R := Finset.range (2 * X.card + 1)
  let bad := X.biUnion (fun p => R.filter (fun k : ℕ => denom (k : ℝ) p = 0))
  have hbad_le : bad.card ≤ 2 * X.card := by
    calc bad.card
        ≤ ∑ p ∈ X, (R.filter (fun k : ℕ => denom (k : ℝ) p = 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ X, 2 := Finset.sum_le_sum (fun p hp => quadratic_roots_card_le_two (hX p hp) R)
      _ = 2 * X.card := by simp [mul_comm]
  have hlt : bad.card < R.card := by
    rw [Finset.card_range]; omega
  have hdiff : (R \ bad).Nonempty := Finset.card_pos.mp (by
    have hsub : bad ⊆ R := by
      intro k hk
      simp only [bad, Finset.mem_biUnion, Finset.mem_filter] at hk
      rcases hk with ⟨_, _, hkR, _⟩
      exact hkR
    rw [Finset.card_sdiff_of_subset hsub]
    omega)
  rcases hdiff with ⟨k, hk⟩
  rw [Finset.mem_sdiff] at hk
  refine ⟨(k : ℝ), fun p hp h0 => hk.2 ?_⟩
  simp only [bad, Finset.mem_biUnion, Finset.mem_filter]
  exact ⟨p, hp, hk.1, h0⟩

/-- Exact preservation of spanned line counts under `projToR2 t`. -/
theorem lineCountR2_projToR2 (t : ℝ) {X : Finset Pt} (hX : Proper X)
    (hden : ∀ p ∈ X, denom t p ≠ 0) {p : Pt} (hp : p ∈ X) :
    lineCountR2 (X.image (projToR2 t)) (projToR2 t p) = projLineCount X p := by
  classical
  have hinj := projToR2_injOn t hX hden
  have herase : (X.image (projToR2 t)).erase (projToR2 t p) = (X.erase p).image (projToR2 t) := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hne, q, hq, rfl⟩
      exact ⟨q, ⟨fun h => hne (by rw [h]), hq⟩, rfl⟩
    · rintro ⟨q, ⟨hne, hq⟩, rfl⟩
      exact ⟨fun h => hne (hinj hq hp h), q, hq, rfl⟩
  have h1 : lineCountR2 (X.image (projToR2 t)) (projToR2 t p) ≤ projLineCount X p := by
    let f : Set (ℝ × ℝ) → Set Pt := fun l =>
      if h : ∃ q ∈ X.erase p, lineR2 (projToR2 t p) (projToR2 t q) = l
      then projLine p (Classical.choose h) else projLine p p
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro l hl
      rw [Finset.mem_coe, spannedLinesR2, herase, Finset.mem_image] at hl
      rcases hl with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
      have hex : ∃ q' ∈ X.erase p, lineR2 (projToR2 t p) (projToR2 t q') =
          lineR2 (projToR2 t p) (projToR2 t q) := ⟨q, hq, rfl⟩
      have hf : f (lineR2 (projToR2 t p) (projToR2 t q)) = projLine p (Classical.choose hex) := by
        dsimp only [f]; exact dite_eq_left_of_eq_true (eq_true hex)
      rw [hf, Finset.mem_coe, spannedProjLines, Finset.mem_image]
      exact ⟨Classical.choose hex, (Classical.choose_spec hex).1, rfl⟩
    · intro l₁ hl₁ l₂ hl₂ heq
      have hex₁ : ∃ q ∈ X.erase p, lineR2 (projToR2 t p) (projToR2 t q) = l₁ := by
        rw [Finset.mem_coe, spannedLinesR2, herase, Finset.mem_image] at hl₁
        rcases hl₁ with ⟨_, ha, rfl⟩
        rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
        exact ⟨q, hq, rfl⟩
      have hex₂ : ∃ q ∈ X.erase p, lineR2 (projToR2 t p) (projToR2 t q) = l₂ := by
        rw [Finset.mem_coe, spannedLinesR2, herase, Finset.mem_image] at hl₂
        rcases hl₂ with ⟨_, ha, rfl⟩
        rcases Finset.mem_image.mp ha with ⟨q, hq, rfl⟩
        exact ⟨q, hq, rfl⟩
      have hf₁ : f l₁ = projLine p (Classical.choose hex₁) := by
        dsimp only [f]; exact dite_eq_left_of_eq_true (eq_true hex₁)
      have hf₂ : f l₂ = projLine p (Classical.choose hex₂) := by
        dsimp only [f]; exact dite_eq_left_of_eq_true (eq_true hex₂)
      rw [hf₁, hf₂] at heq
      set q₁ := Classical.choose hex₁
      set q₂ := Classical.choose hex₂
      have hq₁ := Classical.choose_spec hex₁
      have hq₂ := Classical.choose_spec hex₂
      have hm₁ : q₁ ∈ X := Finset.mem_of_mem_erase hq₁.1
      have hm₂ : q₂ ∈ X := Finset.mem_of_mem_erase hq₂.1
      have hne₁ : q₁ ≠ p := (Finset.mem_erase.mp hq₁.1).1
      have hne₂ : q₂ ≠ p := (Finset.mem_erase.mp hq₂.1).1
      have hns₁ : ¬ SamePt p q₁ := fun hs => hne₁ (hX.2 p hp q₁ hm₁ hs).symm
      have hns₂ : ¬ SamePt p q₂ := fun hs => hne₂ (hX.2 p hp q₂ hm₂ hs).symm
      have hdet : det p q₁ q₂ = 0 :=
        (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 q₁ hm₁) (hX.1 q₂ hm₂) hns₁ hns₂).mp heq
      have hcol : CollinearR2 (projToR2 t p) (projToR2 t q₁) (projToR2 t q₂) :=
        (collinearR2_projToR2_iff t (hden p hp) (hden q₁ hm₁) (hden q₂ hm₂)).mpr hdet
      have hneR₁ : projToR2 t p ≠ projToR2 t q₁ := fun h => hne₁ (hinj hp hm₁ h).symm
      have hneR₂ : projToR2 t p ≠ projToR2 t q₂ := fun h => hne₂ (hinj hp hm₂ h).symm
      rw [← hq₁.2, ← hq₂.2]
      exact (lineR2_eq_iff_collinearR2 hneR₁ hneR₂).mpr hcol
  have h2 : projLineCount X p ≤ lineCountR2 (X.image (projToR2 t)) (projToR2 t p) := by
    refine projLineCount_le_of_label hX hp (fun q => lineR2 (projToR2 t p) (projToR2 t q))
      (spannedLinesR2 (X.image (projToR2 t)) (projToR2 t p)) le_rfl ?_ ?_
    · intro q hq
      simp only [spannedLinesR2, herase, Finset.mem_image]
      exact ⟨projToR2 t q, ⟨q, hq, rfl⟩, rfl⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      have hm₁ : q₁ ∈ X := Finset.mem_of_mem_erase hq₁
      have hm₂ : q₂ ∈ X := Finset.mem_of_mem_erase hq₂
      have hneR₁ : projToR2 t p ≠ projToR2 t q₁ :=
        fun h => (Finset.mem_erase.mp hq₁).1 (hinj hp hm₁ h).symm
      have hneR₂ : projToR2 t p ≠ projToR2 t q₂ :=
        fun h => (Finset.mem_erase.mp hq₂).1 (hinj hp hm₂ h).symm
      have hcol : CollinearR2 (projToR2 t p) (projToR2 t q₁) (projToR2 t q₂) :=
        (lineR2_eq_iff_collinearR2 hneR₁ hneR₂).mp heq
      exact (collinearR2_projToR2_iff t (hden p hp) (hden q₁ hm₁) (hden q₂ hm₂)).mp hcol
  exact le_antisymm h1 h2

/-- **Projective-to-Euclidean `ℝ²` Lift Theorem**: every finite `Proper` set of
integer projective points embeds into `ℝ × ℝ` via an explicit chart `φ = projToR2 t`
preserving cardinality, non-collinearity, and every point's exact spanned line count. -/
theorem exists_euclidean_embedding (X : Finset Pt) (hX : Proper X) :
    ∃ φ : Pt → ℝ × ℝ,
      Set.InjOn φ X ∧
      (X.image φ).card = X.card ∧
      (NonCollinear X → NonCollinearR2 (X.image φ)) ∧
      (∀ p ∈ X, lineCountR2 (X.image φ) (φ p) = projLineCount X p) := by
  classical
  obtain ⟨t, hden⟩ := exists_good_param X hX.1
  refine ⟨projToR2 t, projToR2_injOn t hX hden, ?_, ?_, ?_⟩
  · exact Finset.card_image_of_injOn (projToR2_injOn t hX hden)
  · rintro ⟨p, hp, q, hq, r, hr, hdet⟩
    refine ⟨projToR2 t p, Finset.mem_image_of_mem _ hp,
            projToR2 t q, Finset.mem_image_of_mem _ hq,
            projToR2 t r, Finset.mem_image_of_mem _ hr, ?_⟩
    rw [collinearR2_projToR2_iff t (hden p hp) (hden q hq) (hden r hr)]
    exact hdet
  · intro p hp
    exact lineCountR2_projToR2 t hX hden hp

/-- Corollary lifting a projective upper bound to an existential Euclidean set in `ℝ²`. -/
theorem exists_euclidean_set_le {X : Finset Pt} {n B : ℕ}
    (hX : Proper X) (hcard : X.card = n) (hnc : NonCollinear X)
    (hbound : ∀ p ∈ X, projLineCount X p ≤ B) :
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ B := by
  obtain ⟨φ, _, hφcard, hφnc, hφcnt⟩ := exists_euclidean_embedding X hX
  refine ⟨X.image φ, hφcard.trans hcard, hφnc hnc, ?_⟩
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
  rw [hφcnt p hp]
  exact hbound p hp

/-- Corollary lifting an exact projective maximum line count to an existential
Euclidean set in `ℝ²`. -/
theorem exists_euclidean_set_eq {X : Finset Pt} {n B : ℕ}
    (hX : Proper X) (hcard : X.card = n) (hnc : NonCollinear X)
    (hbound : ∀ p ∈ X, projLineCount X p ≤ B)
    (htight : ∃ p ∈ X, B ≤ projLineCount X p) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = n ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ B) ∧
      (∃ a ∈ P, lineCountR2 P a = B) := by
  obtain ⟨φ, _, hφcard, hφnc, hφcnt⟩ := exists_euclidean_embedding X hX
  rcases htight with ⟨p₀, hp₀, hge⟩
  refine ⟨X.image φ, hφcard.trans hcard, hφnc hnc, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rw [hφcnt p hp]
    exact hbound p hp
  · refine ⟨φ p₀, Finset.mem_image_of_mem _ hp₀, ?_⟩
    rw [hφcnt p₀ hp₀]
    exact le_antisymm (hbound p₀ hp₀) hge

/-- Deleting a point never increases `projLineCount` at any remaining point. -/
theorem projLineCount_erase_le (X : Finset Pt) (p q : Pt) :
    projLineCount (X.erase q) p ≤ projLineCount X p := by
  classical
  refine Finset.card_le_card (Finset.image_subset_image ?_)
  intro r hr
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1,
    Finset.mem_of_mem_erase (Finset.mem_erase.mp hr).2⟩

/-- Deleting a point never increases `lineCountR2` at any remaining Euclidean point. -/
theorem lineCountR2_erase_le (P : Finset (ℝ × ℝ)) (a b : ℝ × ℝ) :
    lineCountR2 (P.erase b) a ≤ lineCountR2 P a := by
  classical
  refine Finset.card_le_card (Finset.image_subset_image ?_)
  intro r hr
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1,
    Finset.mem_of_mem_erase (Finset.mem_erase.mp hr).2⟩

end StrongDirac
