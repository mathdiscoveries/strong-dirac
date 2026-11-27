module

public import StrongDirac.Projective
public import StrongDirac.R15_2_1
public import StrongDirac.HullCert
public import StrongDirac.R17_2_1
public import StrongDirac.TightnessAndMod12

import Mathlib.Tactic

/-!
# Rational Euclidean Realization & All 12/12 Mod-60 Exact Maxima (`StrongDirac.ExactEqualities`)

Completes **100% pure-kernel Lean 4 coverage** of both main theorems (`thm:half` and
`thm:knights`) and all **12/12** residue-class mod-60 exact rational maxima of
`papers/strong-dirac/draft3/hughes-strong-dirac-draft3.tex`:

1. **Rational Projective-to-Euclidean Realization (`ℚ² ⊂ ℝ²`)**:
   - Proves `exists_good_nat_param` (pigeonhole over `ℕ` avoiding all `denom (k : ℝ) p = 0`)
     and `exists_rational_euclidean_embedding` / `exists_rational_euclidean_set_eq`, lifting
     any finite `Proper` integer projective set `X` to a **rational** Euclidean configuration
     `P ⊂ ℚ² ⊂ ℝ²` preserving cardinality, non-collinearity, and every point's exact
     spanned line count `lineCountR2`.
   - Upgrades `R15-2-1` exact tightness (`j ≥ 2`, `n = 12j + 11`, exact `t(P) = 6j + 5`)
     to rational coordinates (`r15_2_1_rational_tight`) and packages Draft 3 Theorem 1
     verbatim (`thm_half`).
2. **Collinear Point Erasure & Exact Preservation (`projLineCount_erase_eq_of_collinear`)**:
   - Proves that erasing `q ∈ X` preserves `projLineCount X p` whenever some third surviving
     point `r ∈ X \ {p, q}` is collinear with `p` and `q` (`det p q r = 0`).
   - Immediately closes all **6 even families** by erasing the diagonal point `(1, 1, b)`:
     - `A - 1`, `B - 1`, `C - 1` retain the maximizing outer axis point `(1, 0, a)` via the
       surviving horizontal `(0, 1, -(s + 1))`.
     - `(B \ D_4) - 1`, `(A \ D_8) - 1`, `(A \ D_4) - 1` retain the maximizing outer knight
       point `(1, 2, m)` via the surviving horizontal `(0, 1, -(3s + 3))`.
3. **Exact Outer-Knight Lower Bounds for `B \ D_4`, `A \ D_8`, `A \ D_4`**:
   - Proves `le_projLineCount_of_zLabel60_hits` on `(1, 2, m)` using the scaled coordinate
     `zLabel60 m q = 60 * (q.2.2 - m * q.1) / (q.2.1 - 2 * q.1)`.
   - Constructs explicit pairwise-disjoint witness families partitioned by residues mod 60
     (and mod 120 on `0 mod 60`), proving exact projective maxima:
     - `familyBE4_knight_lineCount` (`s ≥ 1`, `30s + 31`)
     - `familyAD8_knight_lineCount` (`s ≥ 2`, `30s + 21`)
     - `familyAD4_knight_lineCount` (`s ≥ 2`, `30s + 23`).
4. **All 12 Individual Sharp-Range Rational Exact Maxima & Unified Theorem 2 (`thm:knights`)**:
   - Proves all 12 individual rational exact-equality theorems at their sharpest start ranges
     (`s ≥ 0` for `A, B`; `s ≥ 1` for `C, B \ D_4`; `s ≥ 2` for `A \ D_8, A \ D_4`).
   - Proves `grunbaum_exact_12_mod60` (all 12 exact rational maxima for every `s ≥ 2`) and
     `thm_knights` (residue-class form matching Draft 3 Theorem 2 verbatim for all `n ≥ 68`
     in `{0, 1, 8, 9, 52, 53} mod 60` and all `n ≥ 124` in `{4, 5, 44, 45, 48, 49} mod 60`).
-/

@[expose] public section

namespace StrongDirac

namespace ExactEqualities

open StrongDirac.R15 StrongDirac.R17 StrongDirac.TightnessAndMod12

/-! ### Section 1: Rational Projective-to-Euclidean Realization (`ℚ² ⊂ ℝ²`) -/

/-- A point in `ℝ²` with rational coordinates. -/
def IsRationalPt (a : ℝ × ℝ) : Prop :=
  ∃ q : ℚ × ℚ, a = ((q.1 : ℝ), (q.2 : ℝ))

/-- A finite point set in `ℝ²` all of whose points have rational coordinates (`P ⊆ ℚ²`). -/
def IsRationalSet (P : Finset (ℝ × ℝ)) : Prop :=
  ∀ a ∈ P, IsRationalPt a

/-- Rational chart denominator `x + k y + k² z ∈ ℚ` at a natural-number parameter `k`. -/
def denomQ (k : ℕ) (p : Pt) : ℚ :=
  (p.1 : ℚ) + (k : ℚ) * (p.2.1 : ℚ) + (k : ℚ) ^ 2 * (p.2.2 : ℚ)

/-- Explicit rational projective-to-Euclidean map `(y / D_Q, z / D_Q) ∈ ℚ²`. -/
def projToQ2 (k : ℕ) (p : Pt) : ℚ × ℚ :=
  ((p.2.1 : ℚ) / denomQ k p, (p.2.2 : ℚ) / denomQ k p)

lemma projToR2_nat_eq_ratCast (k : ℕ) (p : Pt) :
    projToR2 (k : ℝ) p = (((projToQ2 k p).1 : ℝ), ((projToQ2 k p).2 : ℝ)) := by
  unfold projToR2 projToQ2 denom denomQ
  apply Prod.ext <;> push_cast <;> rfl

lemma isRationalSet_iff_exists_ratFinset (P : Finset (ℝ × ℝ)) :
    IsRationalSet P ↔ ∃ Q : Finset (ℚ × ℚ), P = Q.image (fun q => ((q.1 : ℝ), (q.2 : ℝ))) := by
  classical
  constructor
  · intro hrat
    let f : ℝ × ℝ → ℚ × ℚ := fun a =>
      if h : IsRationalPt a then Classical.choose h else (0, 0)
    refine ⟨P.image f, ?_⟩
    ext a
    simp only [Finset.mem_image]
    constructor
    · intro ha
      have hr : IsRationalPt a := hrat a ha
      refine ⟨f a, ⟨a, ha, rfl⟩, ?_⟩
      have hf : f a = Classical.choose hr := dite_eq_left_of_eq_true (eq_true hr)
      rw [hf]
      exact (Classical.choose_spec hr).symm
    · rintro ⟨q, ⟨b, hb, rfl⟩, rfl⟩
      have hr : IsRationalPt b := hrat b hb
      have hf : f b = Classical.choose hr := dite_eq_left_of_eq_true (eq_true hr)
      have hbeq : b = (((f b).1 : ℝ), ((f b).2 : ℝ)) := by
        rw [hf]; exact Classical.choose_spec hr
      rwa [← hbeq]
  · rintro ⟨Q, rfl⟩ a ha
    rcases Finset.mem_image.mp ha with ⟨q, _, rfl⟩
    exact ⟨q, rfl⟩

/-- Pigeonhole existence of a natural-number parameter `k : ℕ` whose affine chart avoids
every point of `X`, guaranteeing rational image coordinates. -/
theorem exists_good_nat_param (X : Finset Pt) (hX : ∀ p ∈ X, Nonzero p) :
    ∃ k : ℕ, ∀ p ∈ X, denom (k : ℝ) p ≠ 0 := by
  classical
  let R := Finset.range (2 * X.card + 1)
  let bad := X.biUnion (fun p => R.filter (fun k : ℕ => denom (k : ℝ) p = 0))
  have hbad_le : bad.card ≤ 2 * X.card := by
    calc bad.card
        ≤ ∑ p ∈ X, (R.filter (fun k : ℕ => denom (k : ℝ) p = 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ X, 2 := Finset.sum_le_sum (fun p hp => quadratic_roots_card_le_two (hX p hp) R)
      _ = 2 * X.card := by simp [mul_comm]
  have hsub : bad ⊆ R := by
    intro k hk
    simp only [bad, Finset.mem_biUnion, Finset.mem_filter] at hk
    rcases hk with ⟨_, _, hkR, _⟩
    exact hkR
  have hdiff : (R \ bad).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]
    omega)
  rcases hdiff with ⟨k, hk⟩
  rw [Finset.mem_sdiff] at hk
  refine ⟨k, fun p hp h0 => hk.2 ?_⟩
  simp only [bad, Finset.mem_biUnion, Finset.mem_filter]
  exact ⟨p, hp, hk.1, h0⟩

/-- **Rational Projective-to-Euclidean Embedding**: every finite `Proper` integer projective
point set embeds into `ℚ² ⊂ ℝ²` preserving cardinality, non-collinearity, and every point's
exact spanned line count. -/
theorem exists_rational_euclidean_embedding (X : Finset Pt) (hX : Proper X) :
    ∃ φ : Pt → ℝ × ℝ,
      (∀ p ∈ X, IsRationalPt (φ p)) ∧
      Set.InjOn φ X ∧
      (X.image φ).card = X.card ∧
      (NonCollinear X → NonCollinearR2 (X.image φ)) ∧
      (∀ p ∈ X, lineCountR2 (X.image φ) (φ p) = projLineCount X p) := by
  classical
  obtain ⟨k, hden⟩ := exists_good_nat_param X hX.1
  refine ⟨projToR2 (k : ℝ),
    fun p _ => ⟨projToQ2 k p, projToR2_nat_eq_ratCast k p⟩,
    projToR2_injOn (k : ℝ) hX hden,
    Finset.card_image_of_injOn (projToR2_injOn (k : ℝ) hX hden), ?_, ?_⟩
  · rintro ⟨p, hp, q, hq, r, hr, hdet⟩
    refine ⟨projToR2 (k : ℝ) p, Finset.mem_image_of_mem _ hp,
            projToR2 (k : ℝ) q, Finset.mem_image_of_mem _ hq,
            projToR2 (k : ℝ) r, Finset.mem_image_of_mem _ hr, ?_⟩
    rw [collinearR2_projToR2_iff (k : ℝ) (hden p hp) (hden q hq) (hden r hr)]
    exact hdet
  · intro p hp
    exact lineCountR2_projToR2 (k : ℝ) hX hden hp

/-- Lift an exact projective maximum to an existential **rational** Euclidean set in `ℝ²`. -/
theorem exists_rational_euclidean_set_eq {X : Finset Pt} {n B : ℕ}
    (hX : Proper X) (hcard : X.card = n) (hnc : NonCollinear X)
    (hbound : ∀ p ∈ X, projLineCount X p ≤ B)
    (htight : ∃ p ∈ X, B ≤ projLineCount X p) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧
      P.card = n ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ B) ∧
      (∃ a ∈ P, lineCountR2 P a = B) := by
  obtain ⟨φ, hrat, _, hφcard, hφnc, hφcnt⟩ := exists_rational_euclidean_embedding X hX
  rcases htight with ⟨p₀, hp₀, hge⟩
  refine ⟨X.image φ, ?_, hφcard.trans hcard, hφnc hnc, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    exact hrat p hp
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
    rw [hφcnt p hp]
    exact hbound p hp
  · refine ⟨φ p₀, Finset.mem_image_of_mem _ hp₀, ?_⟩
    rw [hφcnt p₀ hp₀]
    exact le_antisymm (hbound p₀ hp₀) hge

/-- **Rational Exact Tightness for `R15-2-1` (`j ≥ 2`)**: for every `j ≥ 2`, there exists an
explicit **rational** non-collinear set `P ⊂ ℚ² ⊂ ℝ²` of `12j + 11` points with exact
maximum spanned line count `t(P) = 6j + 5`. -/
theorem r15_2_1_rational_tight {j : ℕ} (hj : 2 ≤ j) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧
      P.card = 12 * j + 11 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 6 * j + 5) ∧
      (∃ a ∈ P, lineCountR2 P a = 6 * j + 5) := by
  have hK : 6 ≤ Kval j := by unfold Kval; omega
  have hp : (1, 0, -Kval j) ∈ S_K j :=
    mem_S_K_iff.mpr (Or.inl ⟨Kval j, mem_Jset_iff.mpr (by omega), rfl⟩)
  exact exists_rational_euclidean_set_eq (S_K_proper j) (S_K_card hj) (S_K_nonCollinear hj)
    (S_K_lineCount_le hj) ⟨_, hp, le_of_eq (S_K_top_lineCount hj).symm⟩

/-- **Draft 3 Theorem 1 (`thm:half`)**:
1. For every `n ≥ 8`, there exists a non-collinear set `P ⊂ ℝ²` of `n` points with
   `t(P) ≤ ⌊n / 2⌋`.
2. For every `j ≥ 2` (`n = 12j + 11`), there exists an explicit **rational** non-collinear
   configuration `P ⊂ ℚ² ⊂ ℝ²` of size `12j + 11` attaining exact maximum `t(P) = 6j + 5`. -/
theorem thm_half :
    (∀ n : ℕ, 8 ≤ n →
      ∃ P : Finset (ℝ × ℝ),
        P.card = n ∧ NonCollinearR2 P ∧ ∀ a ∈ P, lineCountR2 P a ≤ n / 2) ∧
    (∀ j : ℕ, 2 ≤ j →
      ∃ P : Finset (ℝ × ℝ),
        IsRationalSet P ∧
        P.card = 12 * j + 11 ∧
        NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ 6 * j + 5) ∧
        (∃ a ∈ P, lineCountR2 P a = 6 * j + 5)) :=
  ⟨fun n hn => dirac_counterexample_all_ge_8 n hn, fun _ hj => r15_2_1_rational_tight hj⟩

/-! ### Section 2: Collinear Point Erasure & Exact Preservation of Maximum Line Count -/

/-- If `q ∈ X \ {p}` is collinear with `p` and some third surviving point `r ∈ X \ {p, q}`,
then erasing `q` leaves `projLineCount X p` unchanged. -/
theorem projLineCount_erase_eq_of_collinear {X : Finset Pt} (hX : Proper X)
    {p q r : Pt} (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
    (hqp : q ≠ p) (hrp : r ≠ p) (hrq : r ≠ q) (hdet : det p q r = 0) :
    projLineCount (X.erase q) p = projLineCount X p := by
  classical
  refine le_antisymm (projLineCount_erase_le X p q) ?_
  refine Finset.card_le_card ?_
  intro l hl
  simp only [spannedProjLines, Finset.mem_image, Finset.mem_erase] at hl ⊢
  rcases hl with ⟨u, ⟨hup, huX⟩, rfl⟩
  by_cases huq : u = q
  · subst huq
    have hns_q : ¬ SamePt p u := fun hs => hqp (hX.2 p hp u hq hs).symm
    have hns_r : ¬ SamePt p r := fun hs => hrp (hX.2 p hp r hr hs).symm
    have hleq : projLine p u = projLine p r :=
      (projLine_eq_iff_det_eq_zero (hX.1 p hp) (hX.1 u hq) (hX.1 r hr) hns_q hns_r).mpr hdet
    exact ⟨r, ⟨hrp, hrq, hr⟩, hleq.symm⟩
  · exact ⟨u, ⟨hup, huq, huX⟩, rfl⟩

/-- Combined collinear-erasure rational lift: erasing `q` from an `(n + 1)`-point set `X`
yields a rational `n`-point Euclidean configuration with exact maximum `B`. -/
theorem exists_rational_euclidean_erase_eq {X : Finset Pt} {n B : ℕ} {p q r : Pt}
    (hX : Proper X) (hcard : X.card = n + 1)
    (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
    (hqp : q ≠ p) (hrp : r ≠ p) (hrq : r ≠ q) (hdet : det p q r = 0)
    (hnc : NonCollinear (X.erase q))
    (hbound : ∀ x ∈ X, projLineCount X x ≤ B)
    (hpeq : projLineCount X p = B) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧
      P.card = n ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ B) ∧
      (∃ a ∈ P, lineCountR2 P a = B) := by
  have hcard' : (X.erase q).card = n := by
    rw [Finset.card_erase_of_mem hq, hcard]
    omega
  have hbound' : ∀ x ∈ X.erase q, projLineCount (X.erase q) x ≤ B :=
    fun x hx => (projLineCount_erase_le X x q).trans (hbound x (Finset.mem_of_mem_erase hx))
  have hpeq' : projLineCount (X.erase q) p = B := by
    rw [projLineCount_erase_eq_of_collinear hX hp hq hr hqp hrp hrq hdet, hpeq]
  exact exists_rational_euclidean_set_eq
    (proper_subset hX (Finset.erase_subset q X)) hcard' hnc hbound'
    ⟨p, Finset.mem_erase.mpr ⟨hqp.symm, hp⟩, le_of_eq hpeq'.symm⟩

/-! ### Section 3: Exact Outer-Knight Lower Bounds on `(1, 2, m)` -/

/-- Scaled projective height label `z = 60 * (z_q - m * x_q) / (y_q - 2 * x_q)` on lines
through the outer knight point `(1, 2, m)`, returning `none` for parallel points (`y_q = 2 x_q`). -/
def zLabel60 (m : ℤ) (q : Pt) : Option ℤ :=
  let D := q.2.1 - 2 * q.1
  if D = 0 then none else some (60 * (q.2.2 - m * q.1) / D)

/-- Any finite set `Zwit` of distinct `zLabel60 m` values realized by points of
`X.erase (1, 2, m)` gives a lower bound `Zwit.card ≤ projLineCount X (1, 2, m)`. -/
theorem le_projLineCount_of_zLabel60_hits {X : Finset Pt} (hX : Proper X) {m : ℤ}
    (hp : (1, 2, m) ∈ X)
    (hdvd60 : ∀ q ∈ X, q.2.1 - 2 * q.1 = 0 ∨ (q.2.1 - 2 * q.1) ∣ (60 : ℤ))
    (Zwit : Finset (Option ℤ))
    (hhit : ∀ z ∈ Zwit, ∃ q ∈ X.erase (1, 2, m), zLabel60 m q = z) :
    Zwit.card ≤ projLineCount X (1, 2, m) := by
  classical
  let pick : Option ℤ → Pt := fun z =>
    if h : ∃ q ∈ X.erase (1, 2, m), zLabel60 m q = z then Classical.choose h else (0, 0, 0)
  have hpick : ∀ z ∈ Zwit, pick z ∈ X.erase (1, 2, m) ∧ zLabel60 m (pick z) = z := by
    intro z hz
    have hex := hhit z hz
    have hpeq : pick z = Classical.choose hex := dite_eq_left_of_eq_true (eq_true hex)
    rw [hpeq]
    exact Classical.choose_spec hex
  have hsep : ∀ z₁ ∈ Zwit, ∀ z₂ ∈ Zwit, z₁ ≠ z₂ →
      det (1, 2, m) (pick z₁) (pick z₂) ≠ 0 := by
    intro z₁ hz₁ z₂ hz₂ hne hdet
    apply hne
    have hp₁ := hpick z₁ hz₁
    have hp₂ := hpick z₂ hz₂
    rw [← hp₁.2, ← hp₂.2]
    set q₁ := pick z₁
    set q₂ := pick z₂
    have hm₁ : q₁ ∈ X := Finset.mem_of_mem_erase hp₁.1
    have hm₂ : q₂ ∈ X := Finset.mem_of_mem_erase hp₂.1
    have hq₁ne : q₁ ≠ (1, 2, m) := (Finset.mem_erase.mp hp₁.1).1
    have hq₂ne : q₂ ≠ (1, 2, m) := (Finset.mem_erase.mp hp₂.1).1
    rw [det_one_left] at hdet
    set D₁ : ℤ := q₁.2.1 - 2 * q₁.1
    set D₂ : ℤ := q₂.2.1 - 2 * q₂.1
    have hnz_of_D0 : ∀ {q : Pt}, q ∈ X → q ≠ (1, 2, m) → q.2.1 - 2 * q.1 = 0 →
        q.2.2 - m * q.1 ≠ 0 := by
      intro q hqX hqne hD0 h0
      have hqx : q.1 ≠ 0 := by
        intro hx0
        have hy0 : q.2.1 = 0 := by omega
        have hz0 : q.2.2 = 0 := by rw [hx0, mul_zero, sub_zero] at h0; exact h0
        exact hX.1 q hqX (Prod.ext hx0 (Prod.ext hy0 hz0))
      have hsame : SamePt (1, 2, m) q :=
        ⟨q.1, 1, hqx, one_ne_zero, by ring, by dsimp only; omega, by linear_combination -h0⟩
      exact hqne (hX.2 (1, 2, m) hp q hqX hsame).symm
    unfold zLabel60
    change (if D₁ = 0 then none else some (60 * (q₁.2.2 - m * q₁.1) / D₁)) =
      (if D₂ = 0 then none else some (60 * (q₂.2.2 - m * q₂.1) / D₂))
    by_cases h1 : D₁ = 0
    · have h1_nz : q₁.2.2 - m * q₁.1 ≠ 0 := hnz_of_D0 hm₁ hq₁ne h1
      have h2 : D₂ = 0 := by
        have hmul : D₂ * (q₁.2.2 - m * q₁.1) = 0 := by
          have : D₁ * (q₂.2.2 - m * q₂.1) - D₂ * (q₁.2.2 - m * q₁.1) = 0 := hdet
          rw [h1, zero_mul, zero_sub, neg_eq_zero] at this
          exact this
        exact (mul_eq_zero.mp hmul).resolve_right h1_nz
      simp [h1, h2]
    · have h2 : D₂ ≠ 0 := by
        intro h2z
        have h2_nz : q₂.2.2 - m * q₂.1 ≠ 0 := hnz_of_D0 hm₂ hq₂ne h2z
        have hmul : D₁ * (q₂.2.2 - m * q₂.1) = 0 := by
          have : D₁ * (q₂.2.2 - m * q₂.1) - D₂ * (q₁.2.2 - m * q₁.1) = 0 := hdet
          rw [h2z, zero_mul, sub_zero] at this
          exact this
        exact h1 ((mul_eq_zero.mp hmul).resolve_right h2_nz)
      simp only [h1, h2, ↓reduceIte]
      congr 1
      have hd₁ : D₁ ∣ (60 : ℤ) := (hdvd60 q₁ hm₁).resolve_left h1
      have hd₂ : D₂ ∣ (60 : ℤ) := (hdvd60 q₂ hm₂).resolve_left h2
      have hm1 : D₁ * (60 * (q₁.2.2 - m * q₁.1) / D₁) = 60 * (q₁.2.2 - m * q₁.1) :=
        Int.mul_ediv_cancel' (dvd_mul_of_dvd_left hd₁ _)
      have hm2 : D₂ * (60 * (q₂.2.2 - m * q₂.1) / D₂) = 60 * (q₂.2.2 - m * q₂.1) :=
        Int.mul_ediv_cancel' (dvd_mul_of_dvd_left hd₂ _)
      have hscaled : D₁ * D₂ *
          ((60 * (q₂.2.2 - m * q₂.1) / D₂) - (60 * (q₁.2.2 - m * q₁.1) / D₁)) = 0 := by
        calc D₁ * D₂ *
              ((60 * (q₂.2.2 - m * q₂.1) / D₂) - (60 * (q₁.2.2 - m * q₁.1) / D₁))
            = D₁ * (D₂ * (60 * (q₂.2.2 - m * q₂.1) / D₂)) -
              D₂ * (D₁ * (60 * (q₁.2.2 - m * q₁.1) / D₁)) := by ring
          _ = D₁ * (60 * (q₂.2.2 - m * q₂.1)) - D₂ * (60 * (q₁.2.2 - m * q₁.1)) := by
              rw [hm1, hm2]
          _ = 60 * (D₁ * (q₂.2.2 - m * q₂.1) - D₂ * (q₁.2.2 - m * q₁.1)) := by ring
          _ = 0 := by rw [hdet]; ring
      have hdiff0 := (mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero h1 h2)
      omega
  have hinj : Set.InjOn (fun z => projLine (1, 2, m) (pick z)) Zwit := by
    intro z₁ hz₁ z₂ hz₂ heq
    by_contra hne
    have hp₁ := hpick z₁ hz₁
    have hp₂ := hpick z₂ hz₂
    have hm₁ : pick z₁ ∈ X := Finset.mem_of_mem_erase hp₁.1
    have hm₂ : pick z₂ ∈ X := Finset.mem_of_mem_erase hp₂.1
    have hns₁ : ¬ SamePt (1, 2, m) (pick z₁) :=
      fun hs => (Finset.mem_erase.mp hp₁.1).1 (hX.2 (1, 2, m) hp (pick z₁) hm₁ hs).symm
    have hns₂ : ¬ SamePt (1, 2, m) (pick z₂) :=
      fun hs => (Finset.mem_erase.mp hp₂.1).1 (hX.2 (1, 2, m) hp (pick z₂) hm₂ hs).symm
    have hdet : det (1, 2, m) (pick z₁) (pick z₂) = 0 :=
      (projLine_eq_iff_det_eq_zero (hX.1 _ hp) (hX.1 _ hm₁) (hX.1 _ hm₂) hns₁ hns₂).mp heq
    exact hsep z₁ hz₁ z₂ hz₂ hne hdet
  refine Finset.card_le_card_of_injOn (fun z => projLine (1, 2, m) (pick z)) ?_ hinj
  intro z hz
  simp only [spannedProjLines, Finset.mem_coe, Finset.mem_image]
  exact ⟨pick z, (hpick z hz).1, rfl⟩

private lemma knightSet_dvd60 {a e b m : ℕ} :
    ∀ q ∈ knightSet a e b m, q.2.1 - 2 * q.1 = 0 ∨ (q.2.1 - 2 * q.1) ∣ (60 : ℤ) := by
  intro q hq
  rcases mem_knightSet_iff.mp hq with
    ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
    ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl
  · exact Or.inr ⟨-30, by norm_num⟩
  · exact Or.inr ⟨60, by norm_num⟩
  · exact Or.inr ⟨-60, by norm_num⟩
  · exact Or.inr ⟨-20, by norm_num⟩
  · exact Or.inl (by norm_num)
  · exact Or.inr ⟨-15, by norm_num⟩
  · exact Or.inr ⟨-20, by norm_num⟩
  · exact Or.inr ⟨-12, by norm_num⟩
  · exact Or.inl (by norm_num)

private lemma disj_of_pred {A B : Finset ℤ} (P : ℤ → Prop)
    (hA : ∀ z ∈ A, P z) (hB : ∀ z ∈ B, ¬ P z) : Disjoint A B :=
  Finset.disjoint_left.mpr fun z hzA hzB => hB z hzB (hA z hzA)

private lemma card_union9_of_mod60
    {Z1 Z2 Z3 Z4a Z4b Z5_12 Z5_24 Z5_36 Z5_48 : Finset ℤ} {p1 p2 : ℤ}
    (hp : p1 ≠ p2)
    (h1 : ∀ z ∈ Z1, z % 60 = 0 ∧ (z / 60) % 2 = p1)
    (h2 : ∀ z ∈ Z2, z % 60 = 0 ∧ (z / 60) % 2 = p2)
    (h3 : ∀ z ∈ Z3, z % 60 = 30)
    (h4a : ∀ z ∈ Z4a, z % 60 = 40)
    (h4b : ∀ z ∈ Z4b, z % 60 = 20)
    (h5_12 : ∀ z ∈ Z5_12, z % 60 = 12)
    (h5_24 : ∀ z ∈ Z5_24, z % 60 = 24)
    (h5_36 : ∀ z ∈ Z5_36, z % 60 = 36)
    (h5_48 : ∀ z ∈ Z5_48, z % 60 = 48) :
    (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48).card =
      Z1.card + Z2.card + Z3.card + Z4a.card + Z4b.card +
      Z5_12.card + Z5_24.card + Z5_36.card + Z5_48.card := by
  have d12 : Disjoint Z1 Z2 :=
    disj_of_pred (fun z => (z / 60) % 2 = p1) (fun z hz => (h1 z hz).2)
      (fun z hz => by have := (h2 z hz).2; omega)
  have d12_3 : Disjoint (Z1 ∪ Z2) Z3 :=
    disj_of_pred (fun z => z % 60 = 0)
      (fun z hz => by rcases Finset.mem_union.mp hz with h | h; exact (h1 z h).1; exact (h2 z h).1)
      (fun z hz => by have := h3 z hz; omega)
  have d123_4a : Disjoint (Z1 ∪ Z2 ∪ Z3) Z4a :=
    disj_of_pred (fun z => z % 60 ≠ 40)
      (fun z hz => by
        simp only [Finset.mem_union] at hz
        rcases hz with (h | h) | h
        · have := (h1 z h).1; omega
        · have := (h2 z h).1; omega
        · have := h3 z h; omega)
      (fun z hz => not_not.mpr (h4a z hz))
  have d4b : Disjoint (Z1 ∪ Z2 ∪ Z3 ∪ Z4a) Z4b :=
    disj_of_pred (fun z => z % 60 ≠ 20)
      (fun z hz => by
        simp only [Finset.mem_union] at hz
        rcases hz with ((h | h) | h) | h
        · have := (h1 z h).1; omega
        · have := (h2 z h).1; omega
        · have := h3 z h; omega
        · have := h4a z h; omega)
      (fun z hz => not_not.mpr (h4b z hz))
  have d5_12 : Disjoint (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b) Z5_12 :=
    disj_of_pred (fun z => z % 60 ≠ 12)
      (fun z hz => by
        simp only [Finset.mem_union] at hz
        rcases hz with (((h | h) | h) | h) | h
        · have := (h1 z h).1; omega
        · have := (h2 z h).1; omega
        · have := h3 z h; omega
        · have := h4a z h; omega
        · have := h4b z h; omega)
      (fun z hz => not_not.mpr (h5_12 z hz))
  have d5_24 : Disjoint (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12) Z5_24 :=
    disj_of_pred (fun z => z % 60 ≠ 24)
      (fun z hz => by
        simp only [Finset.mem_union] at hz
        rcases hz with ((((h | h) | h) | h) | h) | h
        · have := (h1 z h).1; omega
        · have := (h2 z h).1; omega
        · have := h3 z h; omega
        · have := h4a z h; omega
        · have := h4b z h; omega
        · have := h5_12 z h; omega)
      (fun z hz => not_not.mpr (h5_24 z hz))
  have d5_36 : Disjoint (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24) Z5_36 :=
    disj_of_pred (fun z => z % 60 ≠ 36)
      (fun z hz => by
        simp only [Finset.mem_union] at hz
        rcases hz with (((((h | h) | h) | h) | h) | h) | h
        · have := (h1 z h).1; omega
        · have := (h2 z h).1; omega
        · have := h3 z h; omega
        · have := h4a z h; omega
        · have := h4b z h; omega
        · have := h5_12 z h; omega
        · have := h5_24 z h; omega)
      (fun z hz => not_not.mpr (h5_36 z hz))
  have d5_48 : Disjoint (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36) Z5_48 :=
    disj_of_pred (fun z => z % 60 ≠ 48)
      (fun z hz => by
        simp only [Finset.mem_union] at hz
        rcases hz with ((((((h | h) | h) | h) | h) | h) | h) | h
        · have := (h1 z h).1; omega
        · have := (h2 z h).1; omega
        · have := h3 z h; omega
        · have := h4a z h; omega
        · have := h4b z h; omega
        · have := h5_12 z h; omega
        · have := h5_24 z h; omega
        · have := h5_36 z h; omega)
      (fun z hz => not_not.mpr (h5_48 z hz))
  rw [Finset.card_union_of_disjoint d5_48, Finset.card_union_of_disjoint d5_36,
      Finset.card_union_of_disjoint d5_24, Finset.card_union_of_disjoint d5_12,
      Finset.card_union_of_disjoint d4b, Finset.card_union_of_disjoint d123_4a,
      Finset.card_union_of_disjoint d12_3, Finset.card_union_of_disjoint d12]

/-- Shared witness realizations for Classes 1, 2, 3, and 4a on the outer knight `(1, 2, m)`
in `knightSet a e b m \ D` whenever `D ⊆ knightD8 (m - 2)` and `s ≥ 1`, `δ ≤ 1`. -/
private lemma knight_outer_core_hits {s δ : ℕ} (hs : 1 ≤ s) (hδ : δ ≤ 1)
    {D : Finset Pt} (hD : D ⊆ knightD8 ((5 * s + 1 + 2 * δ : ℕ) : ℤ)) :
    let a := 9 * s + 7 + 2 * δ
    let e := 3 * s + 2
    let b := 8 * s + 6 + 2 * δ
    let m := 5 * s + 3 + 2 * δ
    let X := knightSet a e b m \ D
    let p0 : Pt := (1, 2, (m : ℤ))
    let Z1 := (Finset.range (11 * s + 9 + 3 * δ)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (a : ℤ))
    let Z2 := (Finset.range (5 * s + 4 + δ)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (e : ℤ))
    let Z3 := (Finset.range (4 * s + 2 + δ)).image (fun k : ℕ => 60 * (k : ℤ) + 90)
    let Z4a := (Finset.range (3 * s + 2 + δ)).image
      (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 2))
    ∀ z ∈ Z1 ∪ Z2 ∪ Z3 ∪ Z4a, ∃ q ∈ X.erase p0, zLabel60 (m : ℤ) q = some z := by
  intro a e b m X p0 Z1 Z2 Z3 Z4a z hz
  have hnotD : ∀ q : Pt, q ∉ knightD8 ((5 * s + 1 + 2 * δ : ℕ) : ℤ) → q ∉ D :=
    fun q hq hmem => hq (hD hmem)
  simp only [Finset.mem_union] at hz
  rcases hz with ((h1 | h2) | h3) | h4a
  · -- Class 1: z = 120 k - 60 a
    rcases Finset.mem_image.mp h1 with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    by_cases hle : k ≤ a
    · let c : ℤ := 2 * (k : ℤ) - (a : ℤ)
      have hc : c ∈ parityRange a := mem_parityRange_iff.mpr (by omega)
      refine ⟨(0, 1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨c, Finset.mem_union_left _ hc, rfl⟩)),
        hnotD _ (by simp [knightD8])⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_zero, sub_zero, one_ne_zero, ↓reduceIte, Int.ediv_one,
        Option.some.injEq]
      dsimp only [c]; ring
    · let c : ℤ := (m : ℤ) + (a : ℤ) - 2 * (k : ℤ)
      have hc : c ∈ parityRange b := mem_parityRange_iff.mpr (by omega)
      refine ⟨(1, 1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))),
        hnotD _ (by simp [knightD8])⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_one, Option.some.injEq,
        show (1 : ℤ) - 2 = -1 by omega, show (-1 : ℤ) ≠ 0 by omega, ↓reduceIte]
      dsimp only [c]; omega
  · -- Class 2: z = 120 k - 60 e
    rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    by_cases hle : k ≤ e
    · let c : ℤ := 2 * (k : ℤ) - (e : ℤ)
      have hc : c ∈ parityRange e := mem_parityRange_iff.mpr (by omega)
      refine ⟨(0, 1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩)),
        hnotD _ (by simp [knightD8])⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_zero, sub_zero, one_ne_zero, ↓reduceIte, Int.ediv_one,
        Option.some.injEq]
      dsimp only [c]; ring
    · let c : ℤ := (m : ℤ) + 2 * (e : ℤ) - 4 * (k : ℤ)
      have hc : c ∈ parityRange a := mem_parityRange_iff.mpr (by omega)
      refine ⟨(1, 0, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_left _ hc, rfl⟩),
        hnotD _ (by simp [knightD8])⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_one, Option.some.injEq,
        show (0 : ℤ) - 2 = -2 by omega, show (-2 : ℤ) ≠ 0 by omega, ↓reduceIte]
      dsimp only [c]; omega
  · -- Class 3: z = 60 k + 90
    rcases Finset.mem_image.mp h3 with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    by_cases hge : s + δ ≤ k + 1
    · let c : ℤ := (m : ℤ) - (2 * (k : ℤ) + 3)
      have hc : c ∈ parityRange e := mem_parityRange_iff.mpr (by omega)
      refine ⟨(1, 0, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inl ⟨c, Finset.mem_union_right _ hc, rfl⟩),
        hnotD _ (by simp [knightD8])⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_one, Option.some.injEq,
        show (0 : ℤ) - 2 = -2 by omega, show (-2 : ℤ) ≠ 0 by omega, ↓reduceIte]
      dsimp only [c]; omega
    · let c : ℤ := (m : ℤ) - (4 * (k : ℤ) + 6)
      have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
      refine ⟨(1, -2, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))),
        hnotD _ (by simp [knightD8]; dsimp only [c]; omega)⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_one, Option.some.injEq,
        show (-2 : ℤ) - 2 = -4 by omega, show (-4 : ℤ) ≠ 0 by omega, ↓reduceIte]
      dsimp only [c]; omega
  · -- Class 4a: z = 20 * (6 j - 3(s + 1) + 2)
    rcases Finset.mem_image.mp h4a with ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    let w : ℤ := 6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 2
    by_cases hle : w ≤ (m : ℤ) + (b : ℤ)
    · let c : ℤ := (m : ℤ) - w
      have hc : c ∈ parityRange b := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
      refine ⟨(1, -1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))),
        hnotD _ (by simp [knightD8])⟩⟩, ?_⟩
      unfold zLabel60; simp only [mul_one, Option.some.injEq,
        show (-1 : ℤ) - 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
      dsimp only [c, w]; omega
    · let c : ℤ := 2 * (m : ℤ) - w
      have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
      refine ⟨(2, 1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))),
        hnotD _ (by simp [knightD8]; dsimp only [c, w]; omega)⟩⟩, ?_⟩
      unfold zLabel60; simp only [Option.some.injEq,
        show (1 : ℤ) - 2 * 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
      dsimp only [c, w]; omega

/-- **Exact Outer-Knight Maximum for `B \ D_4` (`s ≥ 1`)**: `(1, 2, 5s + 5)` lies on **exact**
equality `30s + 31 = G(60s + 65) - 1` spanned lines of `familyBE4 s`. -/
theorem familyBE4_knight_lineCount {s : ℕ} (hs : 1 ≤ s) :
    projLineCount (familyBE4 s) (1, 2, ((5 * s + 5 : ℕ) : ℤ)) = 30 * s + 31 := by
  set a := 9 * s + 9
  set e := 3 * s + 2
  set b := 8 * s + 8
  set m := 5 * s + 5
  set p0 : Pt := (1, 2, (m : ℤ))
  have hm_mem : (m : ℤ) ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
  have hp0 : p0 ∈ familyBE4 s := Finset.mem_sdiff.mpr
    ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm_mem, rfl⟩))))),
     by simp [p0, knightD4, m]; omega⟩
  have hle : projLineCount (familyBE4 s) p0 ≤ 30 * s + 31 := familyBE4_lineCount_le hs p0 hp0
  let Z1 := (Finset.range (11 * s + 12)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (a : ℤ))
  let Z2 := (Finset.range (5 * s + 5)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (e : ℤ))
  let Z3 := (Finset.range (4 * s + 3)).image (fun k : ℕ => 60 * (k : ℤ) + 90)
  let Z4a := (Finset.range (3 * s + 3)).image
    (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 2))
  let Z4b := (Finset.range (3 * s + 3)).image
    (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 4))
  let Z5_12 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 3)))
  let Z5_24 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 1)))
  let Z5_36 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 4)))
  let Z5_48 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 2)))
  let Zall := Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48
  have hZall_card : Zall.card = 30 * s + 30 := by
    have hcard := card_union9_of_mod60 (Z1 := Z1) (Z2 := Z2) (Z3 := Z3) (Z4a := Z4a)
      (Z4b := Z4b) (Z5_12 := Z5_12) (Z5_24 := Z5_24) (Z5_36 := Z5_36) (Z5_48 := Z5_48)
      (p1 := (a : ℤ) % 2) (p2 := (e : ℤ) % 2) (by omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
    have c1 : Z1.card = 11 * s + 12 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c2 : Z2.card = 5 * s + 5 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c3 : Z3.card = 4 * s + 3 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c4a : Z4a.card = 3 * s + 3 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c4b : Z4b.card = 3 * s + 3 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_12 : Z5_12.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_24 : Z5_24.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_36 : Z5_36.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_48 : Z5_48.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    change (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48).card = _
    rw [hcard, c1, c2, c3, c4a, c4b, c5_12, c5_24, c5_36, c5_48]
    omega
  let Zwit : Finset (Option ℤ) := insert none (Zall.image some)
  have hZwit_card : Zwit.card = 30 * s + 31 := by
    rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective ℤ), hZall_card]
  have hge : 30 * s + 31 ≤ projLineCount (familyBE4 s) p0 := by
    rw [← hZwit_card]
    refine le_projLineCount_of_zLabel60_hits
      (proper_subset (knightSet_proper ..) Finset.sdiff_subset) hp0
      (fun q hq => knightSet_dvd60 q (Finset.mem_sdiff.mp hq).1) Zwit ?_
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | himg
    · refine ⟨(0, 0, 1), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))),
        by simp [knightD4]⟩⟩, by simp [zLabel60]⟩
    · rcases Finset.mem_image.mp himg with ⟨v, hv, rfl⟩
      have hcore := knight_outer_core_hits hs (δ := 1) le_rfl
        (D := knightD4 (5 * (s : ℤ) + 3))
        (by
          have heq : ((5 * s + 1 + 2 * 1 : ℕ) : ℤ) = 5 * (s : ℤ) + 3 := by push_cast; ring
          rw [heq]; exact knightD4_subset_knightD8 _)
      have h5hit : ∀ r : ℤ, 0 ≤ r → r ≤ 4 → ∀ j < s + 1,
          ∃ q ∈ (familyBE4 s).erase p0,
            zLabel60 (m : ℤ) q = some (12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + r))) := by
        intro r hr0 hr4 j hj
        let c : ℤ := (m : ℤ) - 2 * (5 * (j : ℤ) + r)
        have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c]; omega)
        refine ⟨(2, -1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))))),
          by simp [knightD4]⟩⟩, ?_⟩
        unfold zLabel60; simp only [Option.some.injEq,
          show (-1 : ℤ) - 2 * 2 = -5 by omega, show (-5 : ℤ) ≠ 0 by omega, ↓reduceIte]
        dsimp only [c]; omega
      simp only [Zall, Finset.mem_union] at hv
      rcases hv with ((((hcore_mem | h4b) | h12) | h24) | h36) | h48
      · exact hcore v (by
          have ha_eq : 9 * s + 7 + 2 * 1 = a := by omega
          have hb_eq : 8 * s + 6 + 2 * 1 = b := by omega
          have hm_eq : 5 * s + 3 + 2 * 1 = m := by omega
          have h11 : 11 * s + 9 + 3 * 1 = 11 * s + 12 := by omega
          have h5 : 5 * s + 4 + 1 = 5 * s + 5 := by omega
          have h4 : 4 * s + 2 + 1 = 4 * s + 3 := by omega
          have h3 : 3 * s + 2 + 1 = 3 * s + 3 := by omega
          simpa only [ha_eq, hb_eq, hm_eq, h11, h5, h4, h3, Finset.mem_union] using hcore_mem)
      · rcases Finset.mem_image.mp h4b with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        let w : ℤ := 6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 4
        by_cases hle' : w ≤ (m : ℤ) + (b : ℤ)
        · let c : ℤ := (m : ℤ) - w
          have hc : c ∈ parityRange b := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
          refine ⟨(1, -1, c), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
            mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))),
            by simp [knightD4]⟩⟩, ?_⟩
          unfold zLabel60; simp only [mul_one, Option.some.injEq,
            show (-1 : ℤ) - 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
          dsimp only [c, w]; omega
        · let c : ℤ := 2 * (m : ℤ) - w
          have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
          refine ⟨(2, 1, c), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
            mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))),
            by simp [knightD4]⟩⟩, ?_⟩
          unfold zLabel60; simp only [Option.some.injEq,
            show (1 : ℤ) - 2 * 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
          dsimp only [c, w]; omega
      · rcases Finset.mem_image.mp h12 with ⟨j, hj, rfl⟩
        exact h5hit 3 (by omega) (by omega) j (Finset.mem_range.mp hj)
      · rcases Finset.mem_image.mp h24 with ⟨j, hj, rfl⟩
        exact h5hit 1 (by omega) (by omega) j (Finset.mem_range.mp hj)
      · rcases Finset.mem_image.mp h36 with ⟨j, hj, rfl⟩
        exact h5hit 4 (by omega) (by omega) j (Finset.mem_range.mp hj)
      · rcases Finset.mem_image.mp h48 with ⟨j, hj, rfl⟩
        exact h5hit 2 (by omega) (by omega) j (Finset.mem_range.mp hj)
  exact le_antisymm hle hge

/-- **Exact Outer-Knight Maximum for `A \ D_8` (`s ≥ 2`)**: `(1, 2, 5s + 3)` lies on **exact**
equality `30s + 21 = G(60s + 45) - 1` spanned lines of `familyAD8 s`. -/
theorem familyAD8_knight_lineCount {s : ℕ} (hs : 2 ≤ s) :
    projLineCount (familyAD8 s) (1, 2, ((5 * s + 3 : ℕ) : ℤ)) = 30 * s + 21 := by
  set a := 9 * s + 7
  set e := 3 * s + 2
  set b := 8 * s + 6
  set m := 5 * s + 3
  set p0 : Pt := (1, 2, (m : ℤ))
  have hm_mem : (m : ℤ) ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
  have hp0 : p0 ∈ familyAD8 s := Finset.mem_sdiff.mpr
    ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm_mem, rfl⟩))))),
     by simp [p0, knightD8, m]; omega⟩
  have hle : projLineCount (familyAD8 s) p0 ≤ 30 * s + 21 := familyAD8_lineCount_le hs p0 hp0
  let Z1 := (Finset.range (11 * s + 9)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (a : ℤ))
  let Z2 := (Finset.range (5 * s + 4)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (e : ℤ))
  let Z3 := (Finset.range (4 * s + 2)).image (fun k : ℕ => 60 * (k : ℤ) + 90)
  let Z4a := (Finset.range (3 * s + 2)).image
    (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 2))
  let Z4b := (Finset.range (3 * s + 1)).image
    (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 4))
  let Z5_12 := (Finset.range s).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 4)))
  let Z5_24 := (Finset.range s).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 2)))
  let Z5_36 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ))))
  let Z5_48 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 3)))
  let Zall := Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48
  have hZall_card : Zall.card = 30 * s + 20 := by
    have hcard := card_union9_of_mod60 (Z1 := Z1) (Z2 := Z2) (Z3 := Z3) (Z4a := Z4a)
      (Z4b := Z4b) (Z5_12 := Z5_12) (Z5_24 := Z5_24) (Z5_36 := Z5_36) (Z5_48 := Z5_48)
      (p1 := (a : ℤ) % 2) (p2 := (e : ℤ) % 2) (by omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
    have c1 : Z1.card = 11 * s + 9 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c2 : Z2.card = 5 * s + 4 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c3 : Z3.card = 4 * s + 2 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c4a : Z4a.card = 3 * s + 2 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c4b : Z4b.card = 3 * s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_12 : Z5_12.card = s := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_24 : Z5_24.card = s := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_36 : Z5_36.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_48 : Z5_48.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    change (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48).card = _
    rw [hcard, c1, c2, c3, c4a, c4b, c5_12, c5_24, c5_36, c5_48]
    omega
  let Zwit : Finset (Option ℤ) := insert none (Zall.image some)
  have hZwit_card : Zwit.card = 30 * s + 21 := by
    rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective ℤ), hZall_card]
  have hge : 30 * s + 21 ≤ projLineCount (familyAD8 s) p0 := by
    rw [← hZwit_card]
    refine le_projLineCount_of_zLabel60_hits
      (proper_subset (knightSet_proper ..) Finset.sdiff_subset) hp0
      (fun q hq => knightSet_dvd60 q (Finset.mem_sdiff.mp hq).1) Zwit ?_
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | himg
    · refine ⟨(0, 0, 1), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))),
        by simp [knightD8]⟩⟩, by simp [zLabel60]⟩
    · rcases Finset.mem_image.mp himg with ⟨v, hv, rfl⟩
      have hcore := knight_outer_core_hits (by omega : 1 ≤ s) (δ := 0) (by omega)
        (D := knightD8 (5 * (s : ℤ) + 1))
        (by
          have heq : ((5 * s + 1 + 2 * 0 : ℕ) : ℤ) = 5 * (s : ℤ) + 1 := by push_cast; ring
          rw [heq])
      have h5hit : ∀ k : ℤ, 0 ≤ k → k ≤ (m : ℤ) → k ≠ 1 → k ≠ (m : ℤ) - 1 →
          ∃ q ∈ (familyAD8 s).erase p0,
            zLabel60 (m : ℤ) q = some (12 * ((m : ℤ) + 2 * k)) := by
        intro k hk0 hkm hk1 hk2
        let c : ℤ := (m : ℤ) - 2 * k
        have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c]; omega)
        refine ⟨(2, -1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))))),
          by simp [knightD8]; dsimp only [c]; omega⟩⟩, ?_⟩
        unfold zLabel60; simp only [Option.some.injEq,
          show (-1 : ℤ) - 2 * 2 = -5 by omega, show (-5 : ℤ) ≠ 0 by omega, ↓reduceIte]
        dsimp only [c]; omega
      simp only [Zall, Finset.mem_union] at hv
      rcases hv with ((((hcore_mem | h4b) | h12) | h24) | h36) | h48
      · exact hcore v (by
          have ha_eq : 9 * s + 7 + 2 * 0 = a := by omega
          have hb_eq : 8 * s + 6 + 2 * 0 = b := by omega
          have hm_eq : 5 * s + 3 + 2 * 0 = m := by omega
          have h11 : 11 * s + 9 + 3 * 0 = 11 * s + 9 := by omega
          have h5 : 5 * s + 4 + 0 = 5 * s + 4 := by omega
          have h4 : 4 * s + 2 + 0 = 4 * s + 2 := by omega
          have h3 : 3 * s + 2 + 0 = 3 * s + 2 := by omega
          simpa only [ha_eq, hb_eq, hm_eq, h11, h5, h4, h3, Finset.mem_union] using hcore_mem)
      · rcases Finset.mem_image.mp h4b with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        let w : ℤ := 6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 4
        by_cases hle' : w ≤ (m : ℤ) + (b : ℤ)
        · let c : ℤ := (m : ℤ) - w
          have hc : c ∈ parityRange b := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
          refine ⟨(1, -1, c), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
            mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))),
            by simp [knightD8]⟩⟩, ?_⟩
          unfold zLabel60; simp only [mul_one, Option.some.injEq,
            show (-1 : ℤ) - 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
          dsimp only [c, w]; omega
        · let c : ℤ := 2 * (m : ℤ) - w
          have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
          refine ⟨(2, 1, c), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
            mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))),
            by simp [knightD8]; dsimp only [c, w]; omega⟩⟩, ?_⟩
          unfold zLabel60; simp only [Option.some.injEq,
            show (1 : ℤ) - 2 * 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
          dsimp only [c, w]; omega
      · rcases Finset.mem_image.mp h12 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ) + 4) (by omega) (by omega) (by omega) (by omega)
      · rcases Finset.mem_image.mp h24 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ) + 2) (by omega) (by omega) (by omega) (by omega)
      · rcases Finset.mem_image.mp h36 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ)) (by omega) (by omega) (by omega) (by omega)
      · rcases Finset.mem_image.mp h48 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ) + 3) (by omega) (by omega) (by omega) (by omega)
  exact le_antisymm hle hge

/-- **Exact Outer-Knight Maximum for `A \ D_4` (`s ≥ 2`)**: `(1, 2, 5s + 3)` lies on **exact**
equality `30s + 23 = G(60s + 49) - 1` spanned lines of `familyAD4 s`. -/
theorem familyAD4_knight_lineCount {s : ℕ} (hs : 2 ≤ s) :
    projLineCount (familyAD4 s) (1, 2, ((5 * s + 3 : ℕ) : ℤ)) = 30 * s + 23 := by
  set a := 9 * s + 7
  set e := 3 * s + 2
  set b := 8 * s + 6
  set m := 5 * s + 3
  set p0 : Pt := (1, 2, (m : ℤ))
  have hm_mem : (m : ℤ) ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
  have hp0 : p0 ∈ familyAD4 s := Finset.mem_sdiff.mpr
    ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm_mem, rfl⟩))))),
     by simp [p0, knightD4, m]; omega⟩
  have hle : projLineCount (familyAD4 s) p0 ≤ 30 * s + 23 := familyAD4_lineCount_le hs p0 hp0
  let Z1 := (Finset.range (11 * s + 9)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (a : ℤ))
  let Z2 := (Finset.range (5 * s + 4)).image (fun k : ℕ => 120 * (k : ℤ) - 60 * (e : ℤ))
  let Z3 := (Finset.range (4 * s + 2)).image (fun k : ℕ => 60 * (k : ℤ) + 90)
  let Z4a := (Finset.range (3 * s + 2)).image
    (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 2))
  let Z4b := (Finset.range (3 * s + 2)).image
    (fun j : ℕ => 20 * (6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 4))
  let Z5_12 := (Finset.range s).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 4)))
  let Z5_24 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 2)))
  let Z5_36 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ))))
  let Z5_48 := (Finset.range (s + 1)).image
    (fun j : ℕ => 12 * ((m : ℤ) + 2 * (5 * (j : ℤ) + 3)))
  let Zall := Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48
  have hZall_card : Zall.card = 30 * s + 22 := by
    have hcard := card_union9_of_mod60 (Z1 := Z1) (Z2 := Z2) (Z3 := Z3) (Z4a := Z4a)
      (Z4b := Z4b) (Z5_12 := Z5_12) (Z5_24 := Z5_24) (Z5_36 := Z5_36) (Z5_48 := Z5_48)
      (p1 := (a : ℤ) % 2) (p2 := (e : ℤ) % 2) (by omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
      (fun z hz => by rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩; omega)
    have c1 : Z1.card = 11 * s + 9 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c2 : Z2.card = 5 * s + 4 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c3 : Z3.card = 4 * s + 2 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c4a : Z4a.card = 3 * s + 2 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c4b : Z4b.card = 3 * s + 2 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_12 : Z5_12.card = s := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_24 : Z5_24.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_36 : Z5_36.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    have c5_48 : Z5_48.card = s + 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
    change (Z1 ∪ Z2 ∪ Z3 ∪ Z4a ∪ Z4b ∪ Z5_12 ∪ Z5_24 ∪ Z5_36 ∪ Z5_48).card = _
    rw [hcard, c1, c2, c3, c4a, c4b, c5_12, c5_24, c5_36, c5_48]
    omega
  let Zwit : Finset (Option ℤ) := insert none (Zall.image some)
  have hZwit_card : Zwit.card = 30 * s + 23 := by
    rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective ℤ), hZall_card]
  have hge : 30 * s + 23 ≤ projLineCount (familyAD4 s) p0 := by
    rw [← hZwit_card]
    refine le_projLineCount_of_zLabel60_hits
      (proper_subset (knightSet_proper ..) Finset.sdiff_subset) hp0
      (fun q hq => knightSet_dvd60 q (Finset.mem_sdiff.mp hq).1) Zwit ?_
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | himg
    · refine ⟨(0, 0, 1), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))),
        by simp [knightD4]⟩⟩, by simp [zLabel60]⟩
    · rcases Finset.mem_image.mp himg with ⟨v, hv, rfl⟩
      have hcore := knight_outer_core_hits (by omega : 1 ≤ s) (δ := 0) (by omega)
        (D := knightD4 (5 * (s : ℤ) + 1))
        (by
          have heq : ((5 * s + 1 + 2 * 0 : ℕ) : ℤ) = 5 * (s : ℤ) + 1 := by push_cast; ring
          rw [heq]; exact knightD4_subset_knightD8 _)
      have h5hit : ∀ k : ℤ, 0 ≤ k → k ≤ (m : ℤ) →
          ∃ q ∈ (familyAD4 s).erase p0,
            zLabel60 (m : ℤ) q = some (12 * ((m : ℤ) + 2 * k)) := by
        intro k hk0 hkm
        let c : ℤ := (m : ℤ) - 2 * k
        have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c]; omega)
        refine ⟨(2, -1, c), Finset.mem_erase.mpr ⟨by simp [p0], Finset.mem_sdiff.mpr ⟨
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))))),
          by simp [knightD4]⟩⟩, ?_⟩
        unfold zLabel60; simp only [Option.some.injEq,
          show (-1 : ℤ) - 2 * 2 = -5 by omega, show (-5 : ℤ) ≠ 0 by omega, ↓reduceIte]
        dsimp only [c]; omega
      simp only [Zall, Finset.mem_union] at hv
      rcases hv with ((((hcore_mem | h4b) | h12) | h24) | h36) | h48
      · exact hcore v (by
          have ha_eq : 9 * s + 7 + 2 * 0 = a := by omega
          have hb_eq : 8 * s + 6 + 2 * 0 = b := by omega
          have hm_eq : 5 * s + 3 + 2 * 0 = m := by omega
          have h11 : 11 * s + 9 + 3 * 0 = 11 * s + 9 := by omega
          have h5 : 5 * s + 4 + 0 = 5 * s + 4 := by omega
          have h4 : 4 * s + 2 + 0 = 4 * s + 2 := by omega
          have h3 : 3 * s + 2 + 0 = 3 * s + 2 := by omega
          simpa only [ha_eq, hb_eq, hm_eq, h11, h5, h4, h3, Finset.mem_union] using hcore_mem)
      · rcases Finset.mem_image.mp h4b with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        let w : ℤ := 6 * (j : ℤ) - 3 * ((s : ℤ) + 1) + 4
        by_cases hle' : w ≤ (m : ℤ) + (b : ℤ)
        · let c : ℤ := (m : ℤ) - w
          have hc : c ∈ parityRange b := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
          refine ⟨(1, -1, c), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
            mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))),
            by simp [knightD4]⟩⟩, ?_⟩
          unfold zLabel60; simp only [mul_one, Option.some.injEq,
            show (-1 : ℤ) - 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
          dsimp only [c, w]; omega
        · let c : ℤ := 2 * (m : ℤ) - w
          have hc : c ∈ parityRange m := mem_parityRange_iff.mpr (by dsimp only [c, w]; omega)
          refine ⟨(2, 1, c), Finset.mem_erase.mpr ⟨by simp, Finset.mem_sdiff.mpr ⟨
            mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))),
            by simp [knightD4]⟩⟩, ?_⟩
          unfold zLabel60; simp only [Option.some.injEq,
            show (1 : ℤ) - 2 * 2 = -3 by omega, show (-3 : ℤ) ≠ 0 by omega, ↓reduceIte]
          dsimp only [c, w]; omega
      · rcases Finset.mem_image.mp h12 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ) + 4) (by omega) (by omega)
      · rcases Finset.mem_image.mp h24 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ) + 2) (by omega) (by omega)
      · rcases Finset.mem_image.mp h36 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ)) (by omega) (by omega)
      · rcases Finset.mem_image.mp h48 with ⟨j, hj, rfl⟩
        rw [Finset.mem_range] at hj
        exact h5hit (5 * (j : ℤ) + 3) (by omega) (by omega)
  exact le_antisymm hle hge

/-! ### Section 4: Projective Even-Family Exact Equalities & All 12/12 Rational Maxima -/

private lemma nonCollinear_knightSdiff_erase_diag {a e b m : ℕ} {D : Finset Pt}
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

private lemma nonCollinear_knightSet_erase_diag (a e b m : ℕ) :
    NonCollinear ((knightSet a e b m).erase (1, 1, (b : ℤ))) := by
  have h := nonCollinear_knightSdiff_erase_diag (a := a) (e := e) (b := b) (m := m) (D := ∅)
    (fun _ => ⟨by simp, by simp⟩) (by simp)
  simpa using h

private lemma nonCollinear_of_erase {X : Finset Pt} {q : Pt}
    (h : NonCollinear (X.erase q)) : NonCollinear X := by
  rcases h with ⟨p, hp, r, hr, u, hu, hdet⟩
  exact ⟨p, Finset.mem_of_mem_erase hp, r, Finset.mem_of_mem_erase hr,
         u, Finset.mem_of_mem_erase hu, hdet⟩

/-- Exact projective maximum for even family `A - 1` (`s ≥ 0`): erasing `(1, 1, 8s + 6)`
preserves `projLineCount = 30s + 24` at `(1, 0, 9s + 7)` via the surviving horizontal
`(0, 1, -(s + 1))`. -/
theorem familyA_erase_diag_top_lineCount (s : ℕ) :
    projLineCount ((familyA s).erase (1, 1, ((8 * s + 6 : ℕ) : ℤ)))
      (1, 0, ((9 * s + 7 : ℕ) : ℤ)) = 30 * s + 24 := by
  have ha : ((9 * s + 7 : ℕ) : ℤ) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 6 : ℕ) : ℤ) ∈ parityRange (8 * s + 6) := mem_parityRange_iff.mpr (by omega)
  have hr : -((s : ℤ) + 1) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have heq := projLineCount_erase_eq_of_collinear (X := familyA s) (knightSet_proper ..)
    (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩))
    (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))))
    (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)))
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
  exact heq.trans (familyA_top_lineCount s)

/-- Exact projective maximum for even family `B - 1` (`s ≥ 0`): erasing `(1, 1, 8s + 8)`
preserves `projLineCount = 30s + 32` at `(1, 0, 9s + 9)` via `(0, 1, -(s + 1))`. -/
theorem familyB_erase_diag_top_lineCount (s : ℕ) :
    projLineCount ((familyB s).erase (1, 1, ((8 * s + 8 : ℕ) : ℤ)))
      (1, 0, ((9 * s + 9 : ℕ) : ℤ)) = 30 * s + 32 := by
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 8 : ℕ) : ℤ) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
  have hr : -((s : ℤ) + 1) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have heq := projLineCount_erase_eq_of_collinear (X := familyB s) (knightSet_proper ..)
    (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩))
    (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))))
    (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)))
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
  exact heq.trans (familyB_top_lineCount s)

/-- Exact projective maximum for even family `C - 1` (`s ≥ 1`): erasing `(1, 1, 8s + 8)`
preserves `projLineCount = 30s + 28` at `(1, 0, 9s + 9)` via `(0, 1, -(s + 1))`. -/
theorem familyC_erase_diag_top_lineCount {s : ℕ} (hs : 1 ≤ s) :
    projLineCount ((familyC s).erase (1, 1, ((8 * s + 8 : ℕ) : ℤ)))
      (1, 0, ((9 * s + 9 : ℕ) : ℤ)) = 30 * s + 28 := by
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 8 : ℕ) : ℤ) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
  have hr : -((s : ℤ) + 1) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have heq := projLineCount_erase_eq_of_collinear (X := familyC s)
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩), by simp [knightD8]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD8]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD8]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
  exact heq.trans (familyC_top_lineCount hs)

/-- Exact projective maximum for even family `(B \ D_4) - 1` (`s ≥ 1`): erasing `(1, 1, 8s + 8)`
preserves `projLineCount = 30s + 31` at `(1, 2, 5s + 5)` via `(0, 1, -(3s + 3))`. -/
theorem familyBE4_erase_diag_knight_lineCount {s : ℕ} (hs : 1 ≤ s) :
    projLineCount ((familyBE4 s).erase (1, 1, ((8 * s + 8 : ℕ) : ℤ)))
      (1, 2, ((5 * s + 5 : ℕ) : ℤ)) = 30 * s + 31 := by
  have hm : ((5 * s + 5 : ℕ) : ℤ) ∈ parityRange (5 * s + 5) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 8 : ℕ) : ℤ) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
  have hr : -(3 * (s : ℤ) + 3) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have heq := projLineCount_erase_eq_of_collinear (X := familyBE4 s)
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD4]; omega⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD4]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD4]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
  exact heq.trans (familyBE4_knight_lineCount hs)

/-- Exact projective maximum for even family `(A \ D_8) - 1` (`s ≥ 2`): erasing `(1, 1, 8s + 6)`
preserves `projLineCount = 30s + 21` at `(1, 2, 5s + 3)` via `(0, 1, -(3s + 3))`. -/
theorem familyAD8_erase_diag_knight_lineCount {s : ℕ} (hs : 2 ≤ s) :
    projLineCount ((familyAD8 s).erase (1, 1, ((8 * s + 6 : ℕ) : ℤ)))
      (1, 2, ((5 * s + 3 : ℕ) : ℤ)) = 30 * s + 21 := by
  have hm : ((5 * s + 3 : ℕ) : ℤ) ∈ parityRange (5 * s + 3) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 6 : ℕ) : ℤ) ∈ parityRange (8 * s + 6) := mem_parityRange_iff.mpr (by omega)
  have hr : -(3 * (s : ℤ) + 3) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have heq := projLineCount_erase_eq_of_collinear (X := familyAD8 s)
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD8]; omega⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD8]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD8]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
  exact heq.trans (familyAD8_knight_lineCount hs)

/-- Exact projective maximum for even family `(A \ D_4) - 1` (`s ≥ 2`): erasing `(1, 1, 8s + 6)`
preserves `projLineCount = 30s + 23` at `(1, 2, 5s + 3)` via `(0, 1, -(3s + 3))`. -/
theorem familyAD4_erase_diag_knight_lineCount {s : ℕ} (hs : 2 ≤ s) :
    projLineCount ((familyAD4 s).erase (1, 1, ((8 * s + 6 : ℕ) : ℤ)))
      (1, 2, ((5 * s + 3 : ℕ) : ℤ)) = 30 * s + 23 := by
  have hm : ((5 * s + 3 : ℕ) : ℤ) ∈ parityRange (5 * s + 3) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 6 : ℕ) : ℤ) ∈ parityRange (8 * s + 6) := mem_parityRange_iff.mpr (by omega)
  have hr : -(3 * (s : ℤ) + 3) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have heq := projLineCount_erase_eq_of_collinear (X := familyAD4 s)
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD4]; omega⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD4]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD4]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
  exact heq.trans (familyAD4_knight_lineCount hs)

/-! #### The 12 Individual Rational Exact-Equality Theorems at Sharpest Start Ranges -/

/-- Row 1 (odd): Family `A`, `s ≥ 0`, `n = 60s + 53`, exact rational `t(P) = 30s + 24 = G(n) - 2`. -/
theorem familyA_odd_rational_exact (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 53 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 24) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 24) := by
  have ha : ((9 * s + 7 : ℕ) : ℤ) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 7 : ℕ) : ℤ)) ∈ familyA s :=
    mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  exact exists_rational_euclidean_set_eq (knightSet_proper ..) (familyA_card s)
    (knightSet_nonCollinear ..) (familyA_lineCount_le s)
    ⟨_, hp, le_of_eq (familyA_top_lineCount s).symm⟩

/-- Row 1 (even): Family `A - 1`, `s ≥ 0`, `n = 60s + 52`, exact rational `t(P) = 30s + 24 = G(n) - 2`. -/
theorem familyA_even_rational_exact (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 52 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 24) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 24) := by
  have ha : ((9 * s + 7 : ℕ) : ℤ) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 6 : ℕ) : ℤ) ∈ parityRange (8 * s + 6) := mem_parityRange_iff.mpr (by omega)
  have hr : -((s : ℤ) + 1) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  exact exists_rational_euclidean_erase_eq (knightSet_proper ..) (familyA_card s)
    (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩))
    (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))))
    (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)))
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
    (nonCollinear_knightSet_erase_diag ..) (familyA_lineCount_le s) (familyA_top_lineCount s)

/-- Row 2 (odd): Family `B`, `s ≥ 0`, `n = 60s + 69`, exact rational `t(P) = 30s + 32 = G(n) - 2`. -/
theorem familyB_odd_rational_exact (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 69 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 32) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 32) := by
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 9 : ℕ) : ℤ)) ∈ familyB s :=
    mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  exact exists_rational_euclidean_set_eq (knightSet_proper ..) (familyB_card s)
    (knightSet_nonCollinear ..) (familyB_lineCount_le s)
    ⟨_, hp, le_of_eq (familyB_top_lineCount s).symm⟩

/-- Row 2 (even): Family `B - 1`, `s ≥ 0`, `n = 60s + 68`, exact rational `t(P) = 30s + 32 = G(n) - 2`. -/
theorem familyB_even_rational_exact (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 68 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 32) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 32) := by
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 8 : ℕ) : ℤ) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
  have hr : -((s : ℤ) + 1) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  exact exists_rational_euclidean_erase_eq (knightSet_proper ..) (familyB_card s)
    (mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩))
    (mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))))
    (mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)))
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
    (nonCollinear_knightSet_erase_diag ..) (familyB_lineCount_le s) (familyB_top_lineCount s)

/-- Row 3 (odd): Family `C = B \ D_8`, `s ≥ 1`, `n = 60s + 61`, exact rational `t(P) = 30s + 28 = G(n) - 2`. -/
theorem familyC_odd_rational_exact {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 61 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 28) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 28) := by
  have hnc_e := nonCollinear_knightSdiff_erase_diag (a := 9 * s + 9) (e := 3 * s + 2)
    (b := 8 * s + 8) (m := 5 * s + 5) (D := knightD8 (5 * (s : ℤ) + 3))
    (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8])
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 9 : ℕ) : ℤ)) ∈ familyC s :=
    Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩), by simp [knightD8]⟩
  exact exists_rational_euclidean_set_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyC_card hs)
    (nonCollinear_of_erase hnc_e) (familyC_lineCount_le hs)
    ⟨_, hp, le_of_eq (familyC_top_lineCount hs).symm⟩

/-- Row 3 (even): Family `C - 1`, `s ≥ 1`, `n = 60s + 60`, exact rational `t(P) = 30s + 28 = G(n) - 2`. -/
theorem familyC_even_rational_exact {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 60 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 28) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 28) := by
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 8 : ℕ) : ℤ) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
  have hr : -((s : ℤ) + 1) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  exact exists_rational_euclidean_erase_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyC_card hs)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩), by simp [knightD8]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD8]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD8]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
    (nonCollinear_knightSdiff_erase_diag (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8]))
    (familyC_lineCount_le hs) (familyC_top_lineCount hs)

/-- Row 4 (odd): Family `B \ D_4`, `s ≥ 1`, `n = 60s + 65`, exact rational `t(P) = 30s + 31 = G(n) - 1`. -/
theorem familyBE4_odd_rational_exact {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 65 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 31) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 31) := by
  have hnc_e := nonCollinear_knightSdiff_erase_diag (a := 9 * s + 9) (e := 3 * s + 2)
    (b := 8 * s + 8) (m := 5 * s + 5) (D := knightD4 (5 * (s : ℤ) + 3))
    (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4])
  have hm : ((5 * s + 5 : ℕ) : ℤ) ∈ parityRange (5 * s + 5) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 2, ((5 * s + 5 : ℕ) : ℤ)) ∈ familyBE4 s :=
    Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD4]; omega⟩
  exact exists_rational_euclidean_set_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyBE4_card hs)
    (nonCollinear_of_erase hnc_e) (familyBE4_lineCount_le hs)
    ⟨_, hp, le_of_eq (familyBE4_knight_lineCount hs).symm⟩

/-- Row 4 (even): Family `(B \ D_4) - 1`, `s ≥ 1`, `n = 60s + 64`, exact rational `t(P) = 30s + 31 = G(n) - 1`. -/
theorem familyBE4_even_rational_exact {s : ℕ} (hs : 1 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 64 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 31) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 31) := by
  have hm : ((5 * s + 5 : ℕ) : ℤ) ∈ parityRange (5 * s + 5) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 8 : ℕ) : ℤ) ∈ parityRange (8 * s + 8) := mem_parityRange_iff.mpr (by omega)
  have hr : -(3 * (s : ℤ) + 3) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  exact exists_rational_euclidean_erase_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyBE4_card hs)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD4]; omega⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD4]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD4]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
    (nonCollinear_knightSdiff_erase_diag (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4]))
    (familyBE4_lineCount_le hs) (familyBE4_knight_lineCount hs)

/-- Row 5 (odd): Family `A \ D_8`, `s ≥ 2`, `n = 60s + 45`, exact rational `t(P) = 30s + 21 = G(n) - 1`. -/
theorem familyAD8_odd_rational_exact {s : ℕ} (hs : 2 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 45 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 21) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 21) := by
  have hnc_e := nonCollinear_knightSdiff_erase_diag (a := 9 * s + 7) (e := 3 * s + 2)
    (b := 8 * s + 6) (m := 5 * s + 3) (D := knightD8 (5 * (s : ℤ) + 1))
    (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8])
  have hm : ((5 * s + 3 : ℕ) : ℤ) ∈ parityRange (5 * s + 3) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 2, ((5 * s + 3 : ℕ) : ℤ)) ∈ familyAD8 s :=
    Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD8]; omega⟩
  exact exists_rational_euclidean_set_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyAD8_card hs)
    (nonCollinear_of_erase hnc_e) (familyAD8_lineCount_le hs)
    ⟨_, hp, le_of_eq (familyAD8_knight_lineCount hs).symm⟩

/-- Row 5 (even): Family `(A \ D_8) - 1`, `s ≥ 2`, `n = 60s + 44`, exact rational `t(P) = 30s + 21 = G(n) - 1`. -/
theorem familyAD8_even_rational_exact {s : ℕ} (hs : 2 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 44 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 21) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 21) := by
  have hm : ((5 * s + 3 : ℕ) : ℤ) ∈ parityRange (5 * s + 3) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 6 : ℕ) : ℤ) ∈ parityRange (8 * s + 6) := mem_parityRange_iff.mpr (by omega)
  have hr : -(3 * (s : ℤ) + 3) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  exact exists_rational_euclidean_erase_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyAD8_card hs)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD8]; omega⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD8]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD8]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
    (nonCollinear_knightSdiff_erase_diag (fun _ => ⟨by simp [knightD8], by simp [knightD8]⟩) (by simp [knightD8]))
    (familyAD8_lineCount_le hs) (familyAD8_knight_lineCount hs)

/-- Row 6 (odd): Family `A \ D_4`, `s ≥ 2`, `n = 60s + 49`, exact rational `t(P) = 30s + 23 = G(n) - 1`. -/
theorem familyAD4_odd_rational_exact {s : ℕ} (hs : 2 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 49 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 23) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 23) := by
  have hnc_e := nonCollinear_knightSdiff_erase_diag (a := 9 * s + 7) (e := 3 * s + 2)
    (b := 8 * s + 6) (m := 5 * s + 3) (D := knightD4 (5 * (s : ℤ) + 1))
    (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4])
  have hm : ((5 * s + 3 : ℕ) : ℤ) ∈ parityRange (5 * s + 3) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 2, ((5 * s + 3 : ℕ) : ℤ)) ∈ familyAD4 s :=
    Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD4]; omega⟩
  exact exists_rational_euclidean_set_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyAD4_card hs)
    (nonCollinear_of_erase hnc_e) (familyAD4_lineCount_le hs)
    ⟨_, hp, le_of_eq (familyAD4_knight_lineCount hs).symm⟩

/-- Row 6 (even): Family `(A \ D_4) - 1`, `s ≥ 2`, `n = 60s + 48`, exact rational `t(P) = 30s + 23 = G(n) - 1`. -/
theorem familyAD4_even_rational_exact {s : ℕ} (hs : 2 ≤ s) :
    ∃ P : Finset (ℝ × ℝ),
      IsRationalSet P ∧ P.card = 60 * s + 48 ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 23) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 23) := by
  have hm : ((5 * s + 3 : ℕ) : ℤ) ∈ parityRange (5 * s + 3) := mem_parityRange_iff.mpr (by omega)
  have hb : ((8 * s + 6 : ℕ) : ℤ) ∈ parityRange (8 * s + 6) := mem_parityRange_iff.mpr (by omega)
  have hr : -(3 * (s : ℤ) + 3) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  exact exists_rational_euclidean_erase_eq
    (proper_subset (knightSet_proper ..) Finset.sdiff_subset) (familyAD4_card hs)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hm, rfl⟩))))),
      by simp [knightD4]; omega⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, hb, rfl⟩))), by simp [knightD4]⟩)
    (Finset.mem_sdiff.mpr ⟨mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ hr, rfl⟩)), by simp [knightD4]⟩)
    (by simp) (by simp) (by simp) (by unfold det; push_cast; ring)
    (nonCollinear_knightSdiff_erase_diag (fun _ => ⟨by simp [knightD4], by simp [knightD4]⟩) (by simp [knightD4]))
    (familyAD4_lineCount_le hs) (familyAD4_knight_lineCount hs)

/-! #### Unified Headline Theorems Matching Draft 3 Theorem 2 (`thm:knights`) Verbatim -/

private lemma retag_exact {n B B' : ℕ} (hB : B = B')
    (h : ∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = n ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ B) ∧ (∃ a ∈ P, lineCountR2 P a = B)) :
    ∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = n ∧ NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ B') ∧ (∃ a ∈ P, lineCountR2 P a = B') :=
  hB ▸ h

/-- **All 12/12 Exact Rational Mod-60 Maxima (Draft 3 Theorem 2, parameterized form)**:
For every `s ≥ 2`, there exist **rational** non-collinear configurations `P ⊂ ℚ² ⊂ ℝ²`
of all 12 sizes mod 60 achieving **exact** maximum spanned line count:
- `t(P) = G(P.card) - 2` for `60s + {53, 52, 69, 68, 61, 60}` (classes `0, 1, 8, 9, 52, 53 mod 60`),
- `t(P) = G(P.card) - 1` for `60s + {65, 64, 45, 44, 49, 48}` (classes `4, 5, 44, 45, 48, 49 mod 60`). -/
theorem grunbaum_exact_12_mod60 {s : ℕ} (hs : 2 ≤ s) :
    -- 6 residue classes mod 60 attaining exact t(P) = G(n) - 2:
    ((∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 53 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 2)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 52 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 2)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 69 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 2)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 68 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 2)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 61 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 2)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 60 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 2))) ∧
    -- 6 additional residue classes mod 60 attaining exact t(P) = G(n) - 1:
    ((∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 65 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 1)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 64 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 1)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 45 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 1)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 44 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 1)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 49 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 1)) ∧
     (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = 60 * s + 48 ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - 1))) := by
  have hs1 : 1 ≤ s := by omega
  have liftG : ∀ {n B k : ℕ}, B = grunbaumVal n - k →
      (∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = n ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ B) ∧ (∃ a ∈ P, lineCountR2 P a = B)) →
      ∃ P : Finset (ℝ × ℝ), IsRationalSet P ∧ P.card = n ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - k) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal P.card - k) := by
    rintro n B k rfl ⟨P, hr, hc, hnc, hle, heq⟩
    exact ⟨P, hr, hc, hnc, hc ▸ hle, hc ▸ heq⟩
  refine ⟨⟨
    liftG (by unfold grunbaumVal; omega) (familyA_odd_rational_exact s),
    liftG (by unfold grunbaumVal; omega) (familyA_even_rational_exact s),
    liftG (by unfold grunbaumVal; omega) (familyB_odd_rational_exact s),
    liftG (by unfold grunbaumVal; omega) (familyB_even_rational_exact s),
    liftG (by unfold grunbaumVal; omega) (familyC_odd_rational_exact hs1),
    liftG (by unfold grunbaumVal; omega) (familyC_even_rational_exact hs1)⟩, ⟨
    liftG (by unfold grunbaumVal; omega) (familyBE4_odd_rational_exact hs1),
    liftG (by unfold grunbaumVal; omega) (familyBE4_even_rational_exact hs1),
    liftG (by unfold grunbaumVal; omega) (familyAD8_odd_rational_exact hs),
    liftG (by unfold grunbaumVal; omega) (familyAD8_even_rational_exact hs),
    liftG (by unfold grunbaumVal; omega) (familyAD4_odd_rational_exact hs),
    liftG (by unfold grunbaumVal; omega) (familyAD4_even_rational_exact hs)⟩⟩

/-- **Draft 3 Theorem 2 (`thm:knights`, verbatim residue-class form)**:
- For every `n ≥ 68` with `n % 60 ∈ {0, 1, 8, 9, 52, 53}`, there exists a **rational**
  non-collinear configuration `P ⊂ ℚ² ⊂ ℝ²` of `n` points with exact maximum
  `t(P) = G(n) - 2`.
- For every `n ≥ 124` with `n % 60 ∈ {4, 5, 44, 45, 48, 49}`, there exists a **rational**
  non-collinear configuration `P ⊂ ℚ² ⊂ ℝ²` of `n` points with exact maximum
  `t(P) = G(n) - 1`. -/
theorem thm_knights :
    (∀ n : ℕ, 68 ≤ n →
      (n % 60 = 0 ∨ n % 60 = 1 ∨ n % 60 = 8 ∨ n % 60 = 9 ∨ n % 60 = 52 ∨ n % 60 = 53) →
      ∃ P : Finset (ℝ × ℝ),
        IsRationalSet P ∧ P.card = n ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal n - 2) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal n - 2)) ∧
    (∀ n : ℕ, 124 ≤ n →
      (n % 60 = 4 ∨ n % 60 = 5 ∨ n % 60 = 44 ∨ n % 60 = 45 ∨ n % 60 = 48 ∨ n % 60 = 49) →
      ∃ P : Finset (ℝ × ℝ),
        IsRationalSet P ∧ P.card = n ∧ NonCollinearR2 P ∧
        (∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal n - 1) ∧
        (∃ a ∈ P, lineCountR2 P a = grunbaumVal n - 1)) := by
  constructor
  · intro n hn hmod
    rcases hmod with h0 | h1 | h8 | h9 | h52 | h53
    · have hs : 1 ≤ n / 60 - 1 := by omega
      have hne : n = 60 * (n / 60 - 1) + 60 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyC_even_rational_exact hs)
    · have hs : 1 ≤ n / 60 - 1 := by omega
      have hne : n = 60 * (n / 60 - 1) + 61 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyC_odd_rational_exact hs)
    · have hne : n = 60 * (n / 60 - 1) + 68 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyB_even_rational_exact (n / 60 - 1))
    · have hne : n = 60 * (n / 60 - 1) + 69 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyB_odd_rational_exact (n / 60 - 1))
    · have hne : n = 60 * (n / 60) + 52 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyA_even_rational_exact (n / 60))
    · have hne : n = 60 * (n / 60) + 53 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyA_odd_rational_exact (n / 60))
  · intro n hn hmod
    rcases hmod with h4 | h5 | h44 | h45 | h48 | h49
    · have hs : 1 ≤ n / 60 - 1 := by omega
      have hne : n = 60 * (n / 60 - 1) + 64 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyBE4_even_rational_exact hs)
    · have hs : 1 ≤ n / 60 - 1 := by omega
      have hne : n = 60 * (n / 60 - 1) + 65 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyBE4_odd_rational_exact hs)
    · have hs : 2 ≤ n / 60 := by omega
      have hne : n = 60 * (n / 60) + 44 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyAD8_even_rational_exact hs)
    · have hs : 2 ≤ n / 60 := by omega
      have hne : n = 60 * (n / 60) + 45 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyAD8_odd_rational_exact hs)
    · have hs : 2 ≤ n / 60 := by omega
      have hne : n = 60 * (n / 60) + 48 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyAD4_even_rational_exact hs)
    · have hs : 2 ≤ n / 60 := by omega
      have hne : n = 60 * (n / 60) + 49 := by omega
      rw [hne]; exact retag_exact (by unfold grunbaumVal; omega) (familyAD4_odd_rational_exact hs)

end ExactEqualities

end StrongDirac
