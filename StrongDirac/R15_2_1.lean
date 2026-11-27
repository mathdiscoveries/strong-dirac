module

public import StrongDirac.Projective
public import Mathlib.Data.Int.Interval

import Mathlib.Tactic

/-!
# Unconditional Proof of `R15-2-1`: Dirac Counterexamples for All `n = 12j + 11` (`j ≥ 2`)

Formalizes the infinite family `S_K` (`K = 2j + 2`, even `K ≥ 6`, `n = 6K - 1 = 12j + 11`)
answering the open case `n = 12k + 11` (`k ≥ 4`) of Akiyama, Ito, Kobayashi, and Nakamura
(*Graphs and Combinatorics* 27 (2011) 321–326):
- `S_K j` is a `Proper`, `NonCollinear` projective set of `12j + 11` points;
- every point `p ∈ S_K j` lies on at most `6j + 5 = (n - 1) / 2` spanned projective lines;
- via `exists_euclidean_set_le`, for every `j ≥ 2` there exists a non-collinear Euclidean
  point set `P : Finset (ℝ × ℝ)` of cardinality `12j + 11` with `lineCountR2 P a ≤ 6j + 5`
  for every `a ∈ P` (`r15_2_1_euclidean`).
-/

@[expose] public section

namespace StrongDirac

namespace R15

/-- Integer parameter `K = 2j + 2` (even, `K ≥ 6` for `j ≥ 2`). -/
def Kval (j : ℕ) : ℤ := 2 * (j : ℤ) + 2

/-- Index set `J(K) = [-K, K] \ {K - 1, 1 - K, 1}`. -/
def Jset (K : ℤ) : Finset ℤ :=
  (((Finset.Icc (-K) K).erase (K - 1)).erase (1 - K)).erase 1

/-- Index set `JZ(K) = [-K, K] \ {K - 1, 1 - K}`. -/
def JZset (K : ℤ) : Finset ℤ :=
  ((Finset.Icc (-K) K).erase (K - 1)).erase (1 - K)

/-- `X`-axis points `(1, 0, -c)` for `c ∈ J(K)`. -/
def Xpts (K : ℤ) : Finset Pt := (Jset K).image (fun c => (1, 0, -c))

/-- `Y`-axis points `(0, 1, -c)` for `c ∈ J(K)`. -/
def Ypts (K : ℤ) : Finset Pt := (Jset K).image (fun c => (0, 1, -c))

/-- Diagonal points `(1, 1, -c)` for `c ∈ JZ(K)`. -/
def Zpts (K : ℤ) : Finset Pt := (JZset K).image (fun c => (1, 1, -c))

/-- The four median/infinity points `{(1,-1,0), (1,2,0), (2,1,0), (0,0,1)}`. -/
def Mpts : Finset Pt := {(1, -1, 0), (1, 2, 0), (2, 1, 0), (0, 0, 1)}

/-- The `R15-2-1` projective point set `S_K` for `K = 2j + 2` (`|S_K j| = 12j + 11`). -/
def S_K (j : ℕ) : Finset Pt :=
  let K := Kval j
  Xpts K ∪ Ypts K ∪ Zpts K ∪ Mpts

/-! ### Membership, Cardinality, `Proper`, and `NonCollinear` -/

lemma mem_Jset_iff {K c : ℤ} :
    c ∈ Jset K ↔ -K ≤ c ∧ c ≤ K ∧ c ≠ K - 1 ∧ c ≠ 1 - K ∧ c ≠ 1 := by
  simp only [Jset, Finset.mem_erase, Finset.mem_Icc]
  tauto

lemma mem_JZset_iff {K c : ℤ} :
    c ∈ JZset K ↔ -K ≤ c ∧ c ≤ K ∧ c ≠ K - 1 ∧ c ≠ 1 - K := by
  simp only [JZset, Finset.mem_erase, Finset.mem_Icc]
  tauto

lemma mem_S_K_iff {j : ℕ} {p : Pt} :
    p ∈ S_K j ↔
      (∃ c ∈ Jset (Kval j), p = (1, 0, -c)) ∨
      (∃ c ∈ Jset (Kval j), p = (0, 1, -c)) ∨
      (∃ c ∈ JZset (Kval j), p = (1, 1, -c)) ∨
      p = (1, -1, 0) ∨ p = (1, 2, 0) ∨ p = (2, 1, 0) ∨ p = (0, 0, 1) := by
  simp only [S_K, Xpts, Ypts, Zpts, Mpts, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (((⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩) | (rfl | rfl | rfl | rfl))
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

lemma card_JZset {j : ℕ} (hj : 2 ≤ j) : (JZset (Kval j)).card = 4 * j + 3 := by
  have hK : 6 ≤ Kval j := by unfold Kval; omega
  have h1 : Kval j - 1 ∈ Finset.Icc (-Kval j) (Kval j) := Finset.mem_Icc.mpr (by omega)
  have h2 : 1 - Kval j ∈ (Finset.Icc (-Kval j) (Kval j)).erase (Kval j - 1) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩
  unfold JZset
  rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1, Int.card_Icc]
  unfold Kval
  omega

lemma card_Jset {j : ℕ} (hj : 2 ≤ j) : (Jset (Kval j)).card = 4 * j + 2 := by
  have hK : 6 ≤ Kval j := by unfold Kval; omega
  have hmem : (1 : ℤ) ∈ JZset (Kval j) := mem_JZset_iff.mpr (by omega)
  have hJ : Jset (Kval j) = (JZset (Kval j)).erase 1 := rfl
  rw [hJ, Finset.card_erase_of_mem hmem, card_JZset hj]
  omega

theorem S_K_card {j : ℕ} (hj : 2 ≤ j) : (S_K j).card = 12 * j + 11 := by
  set K := Kval j
  have hX : (Xpts K).card = 4 * j + 2 := by
    rw [Xpts, Finset.card_image_of_injective _ (fun a b h => by simp at h; exact h), card_Jset hj]
  have hY : (Ypts K).card = 4 * j + 2 := by
    rw [Ypts, Finset.card_image_of_injective _ (fun a b h => by simp at h; exact h), card_Jset hj]
  have hZ : (Zpts K).card = 4 * j + 3 := by
    rw [Zpts, Finset.card_image_of_injective _ (fun a b h => by simp at h; exact h), card_JZset hj]
  have hM : Mpts.card = 4 := by decide
  have hdXY : Disjoint (Xpts K) (Ypts K) := by
    rw [Finset.disjoint_left]
    intro p hpX hpY
    simp only [Xpts, Ypts, Finset.mem_image] at hpX hpY
    rcases hpX with ⟨_, _, rfl⟩
    rcases hpY with ⟨_, _, h⟩
    simp at h
  have hdXYZ : Disjoint (Xpts K ∪ Ypts K) (Zpts K) := by
    rw [Finset.disjoint_left]
    intro p hpXY hpZ
    simp only [Xpts, Ypts, Zpts, Finset.mem_union, Finset.mem_image] at hpXY hpZ
    rcases hpZ with ⟨_, _, rfl⟩
    rcases hpXY with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp at h
  have hdXYZM : Disjoint (Xpts K ∪ Ypts K ∪ Zpts K) Mpts := by
    rw [Finset.disjoint_left]
    intro p hp hpM
    simp only [Xpts, Ypts, Zpts, Mpts, Finset.mem_union, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton] at hp hpM
    rcases hpM with rfl | rfl | rfl | rfl <;>
      rcases hp with ((⟨_, _, h⟩ | ⟨_, _, h⟩) | ⟨_, _, h⟩) <;> simp at h
  change (Xpts K ∪ Ypts K ∪ Zpts K ∪ Mpts).card = 12 * j + 11
  rw [Finset.card_union_of_disjoint hdXYZM, Finset.card_union_of_disjoint hdXYZ,
      Finset.card_union_of_disjoint hdXY, hX, hY, hZ, hM]
  omega

theorem S_K_proper (j : ℕ) : Proper (S_K j) := by
  constructor
  · intro p hp
    rcases mem_S_K_iff.mp hp with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
      simp [Nonzero]
  · intro p hp q hq hs
    rcases hs with ⟨a, b, ha, hb, hx, hy, hz⟩
    rcases mem_S_K_iff.mp hp with
      ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    rcases mem_S_K_iff.mp hq with
      ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
    simp only at hx hy hz <;>
    first
    | rfl
    | (exfalso; omega)
    | (have hab : a = b := by omega
       subst hab
       have hc : c₁ = c₂ := by
         have : a * (c₂ - c₁) = 0 := by linear_combination hz
         have h0 := (mul_eq_zero.mp this).resolve_left ha
         omega
       subst hc; rfl)

theorem S_K_nonCollinear {j : ℕ} (hj : 2 ≤ j) : NonCollinear (S_K j) := by
  have hK : 6 ≤ Kval j := by unfold Kval; omega
  have h0J : (0 : ℤ) ∈ Jset (Kval j) := mem_Jset_iff.mpr (by omega)
  refine ⟨(1, 0, 0), ?_, (0, 1, 0), ?_, (0, 0, 1), ?_, ?_⟩
  · exact mem_S_K_iff.mpr (Or.inl ⟨0, h0J, by simp⟩)
  · exact mem_S_K_iff.mpr (Or.inr (Or.inl ⟨0, h0J, by simp⟩))
  · exact mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · decide

/-! ### `(x, y)` Symmetry on `S_K` -/

/-- Canonical projective swap `(x, y, z) ↦ (y, x, z)`, keeping `(1, -1, 0)` in canonical sign. -/
def swapS (p : Pt) : Pt :=
  if p = (1, -1, 0) then (1, -1, 0) else swapXY p

lemma swapS_mem_S_K {j : ℕ} {p : Pt} (hp : p ∈ S_K j) : swapS p ∈ S_K j := by
  rcases mem_S_K_iff.mp hp with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
  · exact mem_S_K_iff.mpr (Or.inr (Or.inl ⟨c, hc, by simp [swapS, swapXY]⟩))
  · exact mem_S_K_iff.mpr (Or.inl ⟨c, hc, by simp [swapS, swapXY]⟩)
  · exact mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [swapS, swapXY]⟩)))
  · exact mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [swapS])))))
  · exact mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [swapS, swapXY])))))))
  · exact mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp [swapS, swapXY]))))))
  · exact mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [swapS, swapXY])))))))

lemma swapS_invol_on_S_K {j : ℕ} {p : Pt} (hp : p ∈ S_K j) : swapS (swapS p) = p := by
  rcases mem_S_K_iff.mp hp with
    ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl <;>
  simp [swapS, swapXY]

lemma det_swapS_eq_zero (a b c : Pt) :
    det (swapS a) (swapS b) (swapS c) = 0 ↔ det a b c = 0 := by
  by_cases ha : a = (1, -1, 0) <;>
  by_cases hb : b = (1, -1, 0) <;>
  by_cases hc : c = (1, -1, 0) <;>
  simp only [swapS, ha, hb, hc, ↓reduceIte, swapXY, det] <;>
  constructor <;> intro h <;> linarith

lemma projLineCount_swapS {j : ℕ} {p : Pt} (hp : p ∈ S_K j) :
    projLineCount (S_K j) (swapS p) = projLineCount (S_K j) p :=
  projLineCount_eq_of_det_equiv (S_K_proper j) hp swapS swapS
    (fun _ hq => swapS_mem_S_K hq)
    (fun _ hq => swapS_mem_S_K hq)
    (fun _ hq => swapS_invol_on_S_K hq)
    (fun _ hq => swapS_invol_on_S_K hq)
    det_swapS_eq_zero

/-! ### Helper Cardinality Lemmas for Label Sets -/

private lemma card_insert_none_even (E : Finset ℤ) :
    (insert (none : Option ℤ) (E.image (fun y => some (2 * y)))).card ≤ E.card + 1 := by
  calc (insert (none : Option ℤ) (E.image (fun y => some (2 * y)))).card
      ≤ (E.image (fun y => some (2 * y))).card + 1 := Finset.card_insert_le _ _
    _ ≤ E.card + 1 := Nat.add_le_add_right Finset.card_image_le 1

private lemma card_insert_none_odd_even (E : Finset ℤ) (u : ℤ) :
    (insert (none : Option ℤ) (insert (some u) (E.image (fun y => some (2 * y))))).card ≤
      E.card + 2 := by
  calc (insert (none : Option ℤ) (insert (some u) (E.image (fun y => some (2 * y))))).card
      ≤ (insert (some u) (E.image (fun y => some (2 * y)))).card + 1 := Finset.card_insert_le _ _
    _ ≤ ((E.image (fun y => some (2 * y))).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ ≤ E.card + 2 := by have := Finset.card_image_le (f := fun y : ℤ => some (2 * y)) (s := E); omega

private lemma card_Icc_erase_one (a b x : ℤ) (hx : a ≤ x ∧ x ≤ b) :
    ((Finset.Icc a b).erase x).card = (b - a).toNat := by
  have hm : x ∈ Finset.Icc a b := Finset.mem_Icc.mpr hx
  rw [Finset.card_erase_of_mem hm, Int.card_Icc]
  omega

private lemma card_Icc_erase_three (a b x y z : ℤ)
    (hx : a ≤ x ∧ x ≤ b) (hy : a ≤ y ∧ y ≤ b) (hz : a ≤ z ∧ z ≤ b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((((Finset.Icc a b).erase x).erase y).erase z).card = (b - a - 2).toNat := by
  have h1 : x ∈ Finset.Icc a b := Finset.mem_Icc.mpr hx
  have h2 : y ∈ (Finset.Icc a b).erase x := Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_Icc.mpr hy⟩
  have h3 : z ∈ ((Finset.Icc a b).erase x).erase y :=
    Finset.mem_erase.mpr ⟨hyz.symm, Finset.mem_erase.mpr ⟨hxz.symm, Finset.mem_Icc.mpr hz⟩⟩
  rw [Finset.card_erase_of_mem h3, Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1,
      Int.card_Icc]
  omega

/-! ### Spanned Line Bounds for Each Point Class -/

/-- Class 1: `W = (0, 0, 1)` lies on at most `6 ≤ 6j + 5` spanned lines. -/
theorem lineCount_W {j : ℕ} (hj : 2 ≤ j) :
    projLineCount (S_K j) (0, 0, 1) ≤ 6 * j + 5 := by
  have hp : (0, 0, 1) ∈ S_K j :=
    mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  let L : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (2, 1)}
  refine projLineCount_le_of_label (S_K_proper j) hp (fun q => (q.1, q.2.1)) L ?_ ?_ ?_
  · have hcard : L.card = 6 := by decide
    omega
  · intro q hq
    have hqm : q ∈ S_K j := Finset.mem_of_mem_erase hq
    have hqne : q ≠ (0, 0, 1) := (Finset.mem_erase.mp hq).1
    rcases mem_S_K_iff.mp hqm with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl
    · simp [L]
    · simp [L]
    · simp [L]
    · simp [L]
    · simp [L]
    · simp [L]
    · exact absurd rfl hqne
  · intro q₁ _ q₂ _ heq
    have ⟨h1, h2⟩ := Prod.mk.inj heq
    unfold det; rw [h1, h2]; ring

private def labelM1 (q : Pt) : Option ℤ :=
  if q.2.1 + q.1 = 0 then none else some (-(2 * q.2.2) / (q.2.1 + q.1))

/-- Class 2: `M1 = (1, -1, 0)` lies on at most `6j + 5` spanned lines. -/
theorem lineCount_M1 {j : ℕ} (hj : 2 ≤ j) :
    projLineCount (S_K j) (1, -1, 0) ≤ 6 * j + 5 := by
  set K := Kval j
  have hK : 6 ≤ K := by unfold K Kval; omega
  have hp : (1, -1, 0) ∈ S_K j :=
    mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  let E : Finset (Option ℤ) := (JZset K).image (fun v => some (2 * v))
  let O : Finset (Option ℤ) := (Finset.Icc (-(j : ℤ)) ((j : ℤ) - 1)).image (fun k => some (2 * k + 1))
  let L : Finset (Option ℤ) := insert none (E ∪ O)
  refine projLineCount_le_of_label (S_K_proper j) hp labelM1 L ?_ ?_ ?_
  · have hE : E.card ≤ 4 * j + 3 := Finset.card_image_le.trans (le_of_eq (card_JZset hj))
    have hO : O.card ≤ 2 * j := by
      refine Finset.card_image_le.trans ?_
      rw [Int.card_Icc]; omega
    calc L.card
        ≤ (E ∪ O).card + 1 := Finset.card_insert_le _ _
      _ ≤ E.card + O.card + 1 := Nat.add_le_add_right (Finset.card_union_le E O) 1
      _ ≤ (4 * j + 3) + 2 * j + 1 := by omega
      _ ≤ 6 * j + 5 := by omega
  · intro q hq
    have hqm : q ∈ S_K j := Finset.mem_of_mem_erase hq
    have hqne : q ≠ (1, -1, 0) := (Finset.mem_erase.mp hq).1
    rcases mem_S_K_iff.mp hqm with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
    · have hcZ : c ∈ JZset K := Finset.mem_of_mem_erase hc
      have hlab : labelM1 (1, 0, -c) = some (2 * c) := by
        dsimp only [labelM1]; norm_num
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcZ))
    · have hcZ : c ∈ JZset K := Finset.mem_of_mem_erase hc
      have hlab : labelM1 (0, 1, -c) = some (2 * c) := by
        dsimp only [labelM1]; norm_num
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcZ))
    · have hlab : labelM1 (1, 1, -c) = some c := by
        dsimp only [labelM1]; norm_num
      rw [hlab]
      rw [mem_JZset_iff] at hc
      by_cases hev : c % 2 = 0
      · have hv : c / 2 ∈ JZset K := by
          rw [mem_JZset_iff]; unfold K Kval at *; omega
        have h2 : 2 * (c / 2) = c := by omega
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c / 2, hv, by rw [h2]⟩))
      · have hk : (c - 1) / 2 ∈ Finset.Icc (-(j : ℤ)) ((j : ℤ) - 1) := by
          rw [Finset.mem_Icc]; unfold K Kval at *; omega
        have h2 : 2 * ((c - 1) / 2) + 1 = c := by omega
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c - 1) / 2, hk, by rw [h2]⟩))
    · exact absurd rfl hqne
    · have h0Z : (0 : ℤ) ∈ JZset K := mem_JZset_iff.mpr (by omega)
      have hlab : labelM1 (1, 2, 0) = some (2 * 0) := by decide
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0Z))
    · have h0Z : (0 : ℤ) ∈ JZset K := mem_JZset_iff.mpr (by omega)
      have hlab : labelM1 (2, 1, 0) = some (2 * 0) := by decide
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0Z))
    · have hlab : labelM1 (0, 0, 1) = none := by decide
      rw [hlab]; exact Finset.mem_insert_self _ _
  · intro q₁ hq₁ q₂ hq₂ heq
    have hmul : ∀ q ∈ S_K j, ∀ u : ℤ, labelM1 q = some u → (q.2.1 + q.1) * u = -(2 * q.2.2) := by
      intro q hqm u hu
      rcases mem_S_K_iff.mp hqm with
        ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl
      · dsimp only [labelM1] at hu ⊢; norm_num at hu; omega
      · dsimp only [labelM1] at hu ⊢; norm_num at hu; omega
      · dsimp only [labelM1] at hu ⊢; norm_num at hu; omega
      · simp [labelM1] at hu
      · dsimp only [labelM1] at hu ⊢; norm_num at hu; omega
      · dsimp only [labelM1] at hu ⊢; norm_num at hu; omega
      · simp [labelM1] at hu
    have hnone : ∀ q : Pt, labelM1 q = none → q.2.1 + q.1 = 0 := by
      intro q hq
      unfold labelM1 at hq
      split_ifs at hq with h0
      · exact h0
    rw [det_one_left]
    cases h1 : labelM1 q₁ with
    | none =>
      have d1 := hnone q₁ h1
      have d2 := hnone q₂ (heq.symm.trans h1)
      have e1 : q₁.2.1 - (-1) * q₁.1 = 0 := by omega
      have e2 : q₂.2.1 - (-1) * q₂.1 = 0 := by omega
      rw [e1, e2]; ring
    | some u =>
      have m1 := hmul q₁ (Finset.mem_of_mem_erase hq₁) u h1
      have m2 := hmul q₂ (Finset.mem_of_mem_erase hq₂) u (heq.symm.trans h1)
      have h2det : 2 * ((q₁.2.1 - (-1) * q₁.1) * (q₂.2.2 - 0 * q₂.1) -
          (q₂.2.1 - (-1) * q₂.1) * (q₁.2.2 - 0 * q₁.1)) = 0 := by
        linear_combination (q₁.2.1 + q₁.1) * m2 - (q₂.2.1 + q₂.1) * m1
      omega

private def labelM2 (q : Pt) : Option ℤ :=
  if q.2.1 - 2 * q.1 = 0 then none else some ((2 * q.2.2) / (q.2.1 - 2 * q.1))

/-- Class 3: `M2 = (1, 2, 0)` lies on at most `6j + 5` spanned lines (`M3` follows by `swapS`). -/
theorem lineCount_M2 {j : ℕ} (hj : 2 ≤ j) :
    projLineCount (S_K j) (1, 2, 0) ≤ 6 * j + 5 := by
  set K := Kval j
  have hK : 6 ≤ K := by unfold K Kval; omega
  have hp : (1, 2, 0) ∈ S_K j :=
    mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  let E : Finset (Option ℤ) := (JZset K).image (fun v => some (2 * v))
  let O : Finset (Option ℤ) := (Finset.Icc (-(j : ℤ)) ((j : ℤ) - 1)).image (fun k => some (2 * k + 1))
  let L : Finset (Option ℤ) := insert none (E ∪ O)
  refine projLineCount_le_of_label (S_K_proper j) hp labelM2 L ?_ ?_ ?_
  · have hE : E.card ≤ 4 * j + 3 := Finset.card_image_le.trans (le_of_eq (card_JZset hj))
    have hO : O.card ≤ 2 * j := by
      refine Finset.card_image_le.trans ?_
      rw [Int.card_Icc]; omega
    calc L.card
        ≤ (E ∪ O).card + 1 := Finset.card_insert_le _ _
      _ ≤ E.card + O.card + 1 := Nat.add_le_add_right (Finset.card_union_le E O) 1
      _ ≤ (4 * j + 3) + 2 * j + 1 := by omega
      _ ≤ 6 * j + 5 := by omega
  · intro q hq
    have hqm : q ∈ S_K j := Finset.mem_of_mem_erase hq
    have hqne : q ≠ (1, 2, 0) := (Finset.mem_erase.mp hq).1
    rcases mem_S_K_iff.mp hqm with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl | rfl | rfl | rfl
    · have hlab : labelM2 (1, 0, -c) = some c := by
        dsimp only [labelM2]; norm_num; omega
      rw [hlab]
      rw [mem_Jset_iff] at hc
      by_cases hev : c % 2 = 0
      · have hv : c / 2 ∈ JZset K := by
          rw [mem_JZset_iff]; unfold K Kval at *; omega
        have h2 : 2 * (c / 2) = c := by omega
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c / 2, hv, by rw [h2]⟩))
      · have hk : (c - 1) / 2 ∈ Finset.Icc (-(j : ℤ)) ((j : ℤ) - 1) := by
          rw [Finset.mem_Icc]; unfold K Kval at *; omega
        have h2 : 2 * ((c - 1) / 2) + 1 = c := by omega
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c - 1) / 2, hk, by rw [h2]⟩))
    · have hcZ : -c ∈ JZset K := by
        rw [mem_Jset_iff] at hc; rw [mem_JZset_iff]; omega
      have hlab : labelM2 (0, 1, -c) = some (2 * (-c)) := by
        dsimp only [labelM2]; norm_num
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcZ))
    · have hlab : labelM2 (1, 1, -c) = some (2 * c) := by
        dsimp only [labelM2]; norm_num
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
    · have h0Z : (0 : ℤ) ∈ JZset K := mem_JZset_iff.mpr (by omega)
      have hlab : labelM2 (1, -1, 0) = some (2 * 0) := by decide
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0Z))
    · exact absurd rfl hqne
    · have h0Z : (0 : ℤ) ∈ JZset K := mem_JZset_iff.mpr (by omega)
      have hlab : labelM2 (2, 1, 0) = some (2 * 0) := by decide
      rw [hlab]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0Z))
    · have hlab : labelM2 (0, 0, 1) = none := by decide
      rw [hlab]; exact Finset.mem_insert_self _ _
  · intro q₁ hq₁ q₂ hq₂ heq
    have hmul : ∀ q ∈ S_K j, ∀ u : ℤ, labelM2 q = some u → (q.2.1 - 2 * q.1) * u = 2 * q.2.2 := by
      intro q hqm u hu
      rcases mem_S_K_iff.mp hqm with
        ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl
      · dsimp only [labelM2] at hu ⊢; norm_num at hu; omega
      · dsimp only [labelM2] at hu ⊢; norm_num at hu; omega
      · dsimp only [labelM2] at hu ⊢; norm_num at hu; omega
      · dsimp only [labelM2] at hu ⊢; norm_num at hu; omega
      · simp [labelM2] at hu
      · dsimp only [labelM2] at hu ⊢; norm_num at hu; omega
      · simp [labelM2] at hu
    have hnone : ∀ q : Pt, labelM2 q = none → q.2.1 - 2 * q.1 = 0 := by
      intro q hq
      unfold labelM2 at hq
      split_ifs at hq with h0
      · exact h0
    rw [det_one_left]
    cases h1 : labelM2 q₁ with
    | none =>
      have d1 := hnone q₁ h1
      have d2 := hnone q₂ (heq.symm.trans h1)
      rw [d1, d2]; ring
    | some u =>
      have m1 := hmul q₁ (Finset.mem_of_mem_erase hq₁) u h1
      have m2 := hmul q₂ (Finset.mem_of_mem_erase hq₂) u (heq.symm.trans h1)
      have h2det : 2 * ((q₁.2.1 - 2 * q₁.1) * (q₂.2.2 - 0 * q₂.1) -
          (q₂.2.1 - 2 * q₂.1) * (q₁.2.2 - 0 * q₁.1)) = 0 := by
        linear_combination (q₂.2.1 - 2 * q₂.1) * m1 - (q₁.2.1 - 2 * q₁.1) * m2
      omega

/-- Helper label function for `X_i = (1, 0, -i)`: `u(q) = -2(c + i a) / b`. -/
private def labelX (i : ℤ) (q : Pt) : Option ℤ :=
  if q.2.1 = 0 then none else some (-(2 * (q.2.2 + i * q.1)) / q.2.1)

private lemma labelX_coll {j : ℕ} {i : ℤ} {q₁ q₂ : Pt}
    (hq₁ : q₁ ∈ S_K j) (hq₂ : q₂ ∈ S_K j) (heq : labelX i q₁ = labelX i q₂) :
    det (1, 0, -i) q₁ q₂ = 0 := by
  have hmul : ∀ q ∈ S_K j, ∀ u : ℤ, labelX i q = some u → q.2.1 * u = -(2 * (q.2.2 + i * q.1)) := by
    intro q hqm u hu
    rcases mem_S_K_iff.mp hqm with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl
    · simp [labelX] at hu
    · dsimp only [labelX] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelX] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelX] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelX] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelX] at hu ⊢; norm_num at hu; omega
    · simp [labelX] at hu
  have hnone : ∀ q : Pt, labelX i q = none → q.2.1 = 0 := by
    intro q hq
    unfold labelX at hq
    split_ifs at hq with h0
    · exact h0
  rw [det_one_left]
  cases h1 : labelX i q₁ with
  | none =>
    have d1 := hnone q₁ h1
    have d2 := hnone q₂ (heq.symm.trans h1)
    simp [d1, d2]
  | some u =>
    have m1 := hmul q₁ hq₁ u h1
    have m2 := hmul q₂ hq₂ u (heq.symm.trans h1)
    have h2det : 2 * ((q₁.2.1 - 0 * q₁.1) * (q₂.2.2 - (-i) * q₂.1) -
        (q₂.2.1 - 0 * q₂.1) * (q₁.2.2 - (-i) * q₁.1)) = 0 := by
      linear_combination q₁.2.1 * m2 - q₂.2.1 * m1
    omega

/-- Class 4: Every `X_i = (1, 0, -i)` (`i ∈ J(K)`) lies on at most `6j + 5` spanned lines
(`Y_c` follows by `swapS`). -/
theorem lineCount_X {j : ℕ} (hj : 2 ≤ j) {i : ℤ} (hi : i ∈ Jset (Kval j)) :
    projLineCount (S_K j) (1, 0, -i) ≤ 6 * j + 5 := by
  set K := Kval j
  have hK_def : K = 2 * (j : ℤ) + 2 := rfl
  have hK : 6 ≤ K := by omega
  have hp : (1, 0, -i) ∈ S_K j := mem_S_K_iff.mpr (Or.inl ⟨i, hi, rfl⟩)
  have hiB := mem_Jset_iff.mp hi
  have eval_q : ∀ q ∈ (S_K j).erase (1, 0, -i),
      labelX i q = none ∨
      (∃ c ∈ Jset K, labelX i q = some (2 * c)) ∨
      (∃ s ∈ JZset K, labelX i q = some (2 * (s - i))) ∨
      labelX i q = some (2 * i) ∨
      labelX i q = some (-i) ∨
      labelX i q = some (2 * (-2 * i)) := by
    intro q hq
    rcases mem_S_K_iff.mp (Finset.mem_of_mem_erase hq) with
      ⟨c, _, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨s, hs, rfl⟩ | rfl | rfl | rfl | rfl
    · exact Or.inl (by simp [labelX])
    · exact Or.inr (Or.inl ⟨c, hc, by dsimp only [labelX]; norm_num⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, hs, by dsimp only [labelX]; norm_num; ring⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only [labelX]; norm_num))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only [labelX]; norm_num; omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by dsimp only [labelX]; norm_num; ring)))))
    · exact Or.inl (by simp [labelX])
  by_cases hmid : -(K - 4) ≤ i ∧ i ≤ K - 4
  · let lo : ℤ := min (-K) (-K - i)
    let hiI : ℤ := max K (K - i)
    let E : Finset ℤ := Finset.Icc lo hiI
    let L : Finset (Option ℤ) :=
      insert none (insert (some (-i)) (E.image (fun y => some (2 * y))))
    refine projLineCount_le_of_label (S_K_proper j) hp (labelX i) L ?_ ?_
      (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
    · have hE : E.card = (hiI + 1 - lo).toNat := Int.card_Icc lo hiI
      have hL : L.card ≤ E.card + 2 := card_insert_none_odd_even E (-i)
      omega
    · intro q hq
      rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
      · rw [h0]; exact Finset.mem_insert_self _ _
      · rw [hlab]; rw [mem_Jset_iff] at hc
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      · rw [hlab]; rw [mem_JZset_iff] at hs
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      · rw [hlab]
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      · rw [hlab]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [hlab]
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
  · have hcases : i = K - 3 ∨ i = -(K - 3) ∨ i = K - 2 ∨ i = -(K - 2) ∨ i = K ∨ i = -K := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · let E : Finset ℤ := (Finset.Icc (-2 * K + 3) K).erase (K - 1)
      let L : Finset (Option ℤ) :=
        insert none (insert (some (-(K - 3))) (E.image (fun y => some (2 * y))))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelX (K - 3)) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (K - (-2 * K + 3)).toNat :=
          card_Icc_erase_one (-2 * K + 3) K (K - 1) (by omega)
        have hL : L.card ≤ E.card + 2 := card_insert_none_odd_even E (-(K - 3))
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; rw [mem_JZset_iff] at hs
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
    · let E : Finset ℤ := (Finset.Icc (-K) (2 * K - 3)).erase (1 - K)
      let L : Finset (Option ℤ) :=
        insert none (insert (some (-(-(K - 3)))) (E.image (fun y => some (2 * y))))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelX (-(K - 3))) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (2 * K - 3 - (-K)).toNat :=
          card_Icc_erase_one (-K) (2 * K - 3) (1 - K) (by omega)
        have hL : L.card ≤ E.card + 2 := card_insert_none_odd_even E (-(-(K - 3)))
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; rw [mem_JZset_iff] at hs
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
    · let E : Finset ℤ := (Finset.Icc (-2 * K + 2) K).erase (K - 1)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelX (K - 2)) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (K - (-2 * K + 2)).toNat :=
          card_Icc_erase_one (-2 * K + 2) K (K - 1) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]; rw [mem_JZset_iff] at hs
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨-(j : ℤ),
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩, by congr 1; omega⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
    · let E : Finset ℤ := (Finset.Icc (-K) (2 * K - 2)).erase (1 - K)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelX (-(K - 2))) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (2 * K - 2 - (-K)).toNat :=
          card_Icc_erase_one (-K) (2 * K - 2) (1 - K) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]; rw [mem_JZset_iff] at hs
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(j : ℤ),
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩, by congr 1; omega⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
    · let E : Finset ℤ := (((Finset.Icc (-2 * K) K).erase (K - 1)).erase 1).erase (1 - 2 * K)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelX K) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (K - (-2 * K) - 2).toNat :=
          card_Icc_erase_three (-2 * K) K (K - 1) 1 (1 - 2 * K)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]; rw [mem_JZset_iff] at hs
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨-((j : ℤ) + 1),
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩,
            by congr 1⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
    · let E : Finset ℤ := (((Finset.Icc (-K) (2 * K)).erase (1 - K)).erase 1).erase (2 * K - 1)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelX (-K)) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelX_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (2 * K - (-K) - 2).toNat :=
          card_Icc_erase_three (-K) (2 * K) (1 - K) 1 (2 * K - 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨s, hs, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]; rw [mem_JZset_iff] at hs
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(j : ℤ) + 1,
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩,
            by congr 1⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))

/-- Helper label function for `Z_s = (1, 1, -s)`: `u(q) = 2(c + s a) / (b - a)`. -/
private def labelZ (s : ℤ) (q : Pt) : Option ℤ :=
  if q.2.1 - q.1 = 0 then none else some ((2 * (q.2.2 + s * q.1)) / (q.2.1 - q.1))

private lemma labelZ_coll {j : ℕ} {s : ℤ} {q₁ q₂ : Pt}
    (hq₁ : q₁ ∈ S_K j) (hq₂ : q₂ ∈ S_K j) (heq : labelZ s q₁ = labelZ s q₂) :
    det (1, 1, -s) q₁ q₂ = 0 := by
  have hmul : ∀ q ∈ S_K j, ∀ u : ℤ,
      labelZ s q = some u → (q.2.1 - q.1) * u = 2 * (q.2.2 + s * q.1) := by
    intro q hqm u hu
    rcases mem_S_K_iff.mp hqm with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl | rfl | rfl | rfl
    · dsimp only [labelZ] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelZ] at hu ⊢; norm_num at hu; omega
    · simp [labelZ] at hu
    · dsimp only [labelZ] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelZ] at hu ⊢; norm_num at hu; omega
    · dsimp only [labelZ] at hu ⊢; norm_num at hu; omega
    · simp [labelZ] at hu
  have hnone : ∀ q : Pt, labelZ s q = none → q.2.1 - q.1 = 0 := by
    intro q hq
    unfold labelZ at hq
    split_ifs at hq with h0
    · exact h0
  rw [det_one_left]
  cases h1 : labelZ s q₁ with
  | none =>
    have d1 := hnone q₁ h1
    have d2 := hnone q₂ (heq.symm.trans h1)
    have e1 : q₁.2.1 - 1 * q₁.1 = 0 := by omega
    have e2 : q₂.2.1 - 1 * q₂.1 = 0 := by omega
    rw [e1, e2]; ring
  | some u =>
    have m1 := hmul q₁ hq₁ u h1
    have m2 := hmul q₂ hq₂ u (heq.symm.trans h1)
    have h2det : 2 * ((q₁.2.1 - 1 * q₁.1) * (q₂.2.2 - (-s) * q₂.1) -
        (q₂.2.1 - 1 * q₂.1) * (q₁.2.2 - (-s) * q₁.1)) = 0 := by
      linear_combination (q₂.2.1 - q₂.1) * m1 - (q₁.2.1 - q₁.1) * m2
    omega

/-- Class 5: Every `Z_s = (1, 1, -s)` (`s ∈ JZ(K)`) lies on at most `6j + 5` spanned lines. -/
theorem lineCount_Z {j : ℕ} (hj : 2 ≤ j) {s : ℤ} (hs : s ∈ JZset (Kval j)) :
    projLineCount (S_K j) (1, 1, -s) ≤ 6 * j + 5 := by
  set K := Kval j
  have hK_def : K = 2 * (j : ℤ) + 2 := rfl
  have hK : 6 ≤ K := by omega
  have hp : (1, 1, -s) ∈ S_K j := mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inl ⟨s, hs, rfl⟩)))
  have hsB := mem_JZset_iff.mp hs
  have eval_q : ∀ q ∈ (S_K j).erase (1, 1, -s),
      labelZ s q = none ∨
      (∃ c ∈ Jset K, labelZ s q = some (2 * (c - s))) ∨
      (∃ c ∈ Jset K, labelZ s q = some (2 * (-c))) ∨
      labelZ s q = some (-s) ∨
      labelZ s q = some (2 * s) ∨
      labelZ s q = some (2 * (-2 * s)) := by
    intro q hq
    rcases mem_S_K_iff.mp (Finset.mem_of_mem_erase hq) with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨_, _, rfl⟩ | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨c, hc, by dsimp only [labelZ]; norm_num; ring⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, by dsimp only [labelZ]; norm_num⟩))
    · exact Or.inl (by simp [labelZ])
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only [labelZ]; norm_num))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by dsimp only [labelZ]; norm_num)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by dsimp only [labelZ]; norm_num; ring)))))
    · exact Or.inl (by simp [labelZ])
  by_cases hmid : -(K - 4) ≤ s ∧ s ≤ K - 4
  · let lo : ℤ := min (-K) (-K - s)
    let hiI : ℤ := max K (K - s)
    let E : Finset ℤ := Finset.Icc lo hiI
    let L : Finset (Option ℤ) :=
      insert none (insert (some (-s)) (E.image (fun y => some (2 * y))))
    refine projLineCount_le_of_label (S_K_proper j) hp (labelZ s) L ?_ ?_
      (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
    · have hE : E.card = (hiI + 1 - lo).toNat := Int.card_Icc lo hiI
      have hL : L.card ≤ E.card + 2 := card_insert_none_odd_even E (-s)
      omega
    · intro q hq
      rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
      · rw [h0]; exact Finset.mem_insert_self _ _
      · rw [hlab]; rw [mem_Jset_iff] at hc
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      · rw [hlab]; rw [mem_Jset_iff] at hc
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      · rw [hlab]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [hlab]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      · rw [hlab]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
  · have hcases : s = K - 3 ∨ s = -(K - 3) ∨ s = K - 2 ∨ s = -(K - 2) ∨ s = K ∨ s = -K := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · let E : Finset ℤ := (Finset.Icc (-2 * K + 3) K).erase (K - 1)
      let L : Finset (Option ℤ) :=
        insert none (insert (some (-(K - 3))) (E.image (fun y => some (2 * y))))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelZ (K - 3)) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (K - (-2 * K + 3)).toNat :=
          card_Icc_erase_one (-2 * K + 3) K (K - 1) (by omega)
        have hL : L.card ≤ E.card + 2 := card_insert_none_odd_even E (-(K - 3))
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
    · let E : Finset ℤ := (Finset.Icc (-K) (2 * K - 3)).erase (1 - K)
      let L : Finset (Option ℤ) :=
        insert none (insert (some (-(-(K - 3)))) (E.image (fun y => some (2 * y))))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelZ (-(K - 3))) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (2 * K - 3 - (-K)).toNat :=
          card_Icc_erase_one (-K) (2 * K - 3) (1 - K) (by omega)
        have hL : L.card ≤ E.card + 2 := card_insert_none_odd_even E (-(-(K - 3)))
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩)))
    · let E : Finset ℤ := (Finset.Icc (-2 * K + 2) K).erase (K - 1)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelZ (K - 2)) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (K - (-2 * K + 2)).toNat :=
          card_Icc_erase_one (-2 * K + 2) K (K - 1) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨-(j : ℤ),
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩, by congr 1; omega⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
    · let E : Finset ℤ := (Finset.Icc (-K) (2 * K - 2)).erase (1 - K)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelZ (-(K - 2))) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (2 * K - 2 - (-K)).toNat :=
          card_Icc_erase_one (-K) (2 * K - 2) (1 - K) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(j : ℤ),
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩, by congr 1; omega⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩))
    · let E : Finset ℤ := (((Finset.Icc (-2 * K) K).erase (K - 1)).erase (-1)).erase (1 - 2 * K)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelZ K) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (K - (-2 * K) - 2).toNat :=
          card_Icc_erase_three (-2 * K) K (K - 1) (-1) (1 - 2 * K)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨-((j : ℤ) + 1),
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩,
            by congr 1⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
    · let E : Finset ℤ := (((Finset.Icc (-K) (2 * K)).erase (1 - K)).erase (-1)).erase (2 * K - 1)
      let L : Finset (Option ℤ) := insert none (E.image (fun y => some (2 * y)))
      refine projLineCount_le_of_label (S_K_proper j) hp (labelZ (-K)) L ?_ ?_
        (fun q₁ h₁ q₂ h₂ => labelZ_coll (Finset.mem_of_mem_erase h₁) (Finset.mem_of_mem_erase h₂))
      · have hE : E.card = (2 * K - (-K) - 2).toNat :=
          card_Icc_erase_three (-K) (2 * K) (1 - K) (-1) (2 * K - 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hL : L.card ≤ E.card + 1 := card_insert_none_even E
        omega
      · intro q hq
        rcases eval_q q hq with h0 | ⟨c, hc, hlab⟩ | ⟨c, hc, hlab⟩ | hlab | hlab | hlab
        · rw [h0]; exact Finset.mem_insert_self _ _
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]; rw [mem_Jset_iff] at hc
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(j : ℤ) + 1,
            Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩,
            by congr 1⟩)
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))
        · rw [hlab]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
              Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr (by omega)⟩⟩⟩))

/-! ### Main Theorems for `R15-2-1` -/

/-- **Main Projective Theorem (`R15-2-1`)**: for every `j ≥ 2`, every point of `S_K j`
lies on at most `6j + 5 = ((12j + 11) - 1) / 2` spanned projective lines. -/
theorem S_K_lineCount_le {j : ℕ} (hj : 2 ≤ j) :
    ∀ p ∈ S_K j, projLineCount (S_K j) p ≤ 6 * j + 5 := by
  intro p hp
  rcases mem_S_K_iff.mp hp with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨s, hs, rfl⟩ | rfl | rfl | rfl | rfl
  · exact lineCount_X hj hc
  · have hswap : swapS (1, 0, -c) = (0, 1, -c) := by simp [swapS, swapXY]
    rw [← hswap, projLineCount_swapS (mem_S_K_iff.mpr (Or.inl ⟨c, hc, rfl⟩))]
    exact lineCount_X hj hc
  · exact lineCount_Z hj hs
  · exact lineCount_M1 hj
  · exact lineCount_M2 hj
  · have hswap : swapS (1, 2, 0) = (2, 1, 0) := by simp [swapS, swapXY]
    rw [← hswap, projLineCount_swapS (mem_S_K_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]
    exact lineCount_M2 hj
  · exact lineCount_W hj

/-- **Main Euclidean Headline Theorem (`R15-2-1`)**: for every `j ≥ 2`, there exists a
non-collinear set `P` of `12j + 11` points in the Euclidean plane `ℝ²` such that every
point of `P` lies on at most `6j + 5 = (P.card - 1) / 2` distinct lines spanned by `P`.
This settles the open case `n = 12k + 11` (`k ≥ 4`) of Akiyama, Ito, Kobayashi, and
Nakamura (2011). -/
theorem r15_2_1_euclidean {j : ℕ} (hj : 2 ≤ j) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 12 * j + 11 ∧
      NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ 6 * j + 5 :=
  exists_euclidean_set_le (S_K_proper j) (S_K_card hj) (S_K_nonCollinear hj)
    (S_K_lineCount_le hj)

end R15

end StrongDirac
