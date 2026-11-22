module

public import StrongDirac.Projective
public import StrongDirac.HullCert
public import Mathlib.Data.Int.Interval

import Mathlib.Tactic

/-!
# Unconditional Proof of `deficit-5/2 families`: Knight-Lattice Deficit-`5/2` Families

Formalizes both infinite knight-lattice families of `deficit-5/2 families` unconditionally for ALL `s ≥ 0`:
- **Family A** (`(a, e, b, m) = (9s + 7, 3s + 2, 8s + 6, 5s + 3)`):
  `n = 60s + 53` points, non-collinear, maximum spanned line count **equal to**
  `30s + 24 = (n - 5) / 2` (deficit `5/2`).
- **Family B** (`(a, e, b, m) = (9s + 9, 3s + 2, 8s + 8, 5s + 5)`):
  `n = 60s + 69` points, non-collinear, maximum spanned line count **equal to**
  `30s + 32 = (n - 5) / 2` (deficit `5/2`).

Proof architecture (100% pure Lean kernel, zero `sorry`, zero `native_decide`):
1. `knightSet a e b m` construction, `Proper`, `NonCollinear`, and exact cardinality
   `2a + 2e + 2b + 4m + 11` whenever `a % 2 ≠ e % 2`.
2. Full `D_4 × {±1}` coordinate symmetries (`symZ`, `symY`, `symXY`), reducing all 11 point
   pieces to 4 canonical nonnegative classes: `(0, 0, 1)`, `(1, 0, c)`, `(1, 1, c)`, `(1, 2, c)`.
3. Splitting `s = 2t` and `s = 2t + 1` into 4 parity-constant branches, each of the 4 classes
   is certified for ALL `t ≥ 0` by `HullCert.projLineCount_le_of_certifyTarget` with kernel-checked
   `decide` certificates (`16` certificates total).
4. Exact tightness at the top axis point `(1, 0, a)` via explicit disjoint label witnesses of
   cardinality `30s + 24` (Family A) and `30s + 32` (Family B).
5. Projective-to-Euclidean lift (`deficit52_familyA_euclidean`, `deficit52_familyB_euclidean`)
   giving explicit non-collinear Euclidean sets in `ℝ²` attaining deficit `5/2` for every `s ≥ 0`.
-/

@[expose] public section

namespace StrongDirac

namespace DeficitFiveHalves

open HullCert

/-! ### General 4-Parameter Knight-Lattice Point Set -/

/-- The `B + 1` integers `{-B, -B + 2, ..., B - 2, B}` of the same parity as `B`. -/
def parityRange (B : ℕ) : Finset ℤ :=
  (Finset.range (B + 1)).image (fun (i : ℕ) => 2 * (i : ℤ) - (B : ℤ))

lemma mem_parityRange_iff {B : ℕ} {c : ℤ} :
    c ∈ parityRange B ↔ -(B : ℤ) ≤ c ∧ c ≤ (B : ℤ) ∧ c % 2 = (B : ℤ) % 2 := by
  simp only [parityRange, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨by omega, by omega, by omega⟩
  · rintro ⟨hlo, hhi, hpar⟩
    refine ⟨((c + (B : ℤ)) / 2).toNat, ?_, ?_⟩
    · have hnn : 0 ≤ (c + (B : ℤ)) / 2 := Int.ediv_nonneg (by omega) (by omega)
      have h1 : (((c + (B : ℤ)) / 2).toNat : ℤ) = (c + (B : ℤ)) / 2 :=
        Int.toNat_of_nonneg hnn
      have hdiv := Int.mul_ediv_add_emod (c + (B : ℤ)) 2
      have hmod : (c + (B : ℤ)) % 2 = 0 := by omega
      omega
    · have hnn : 0 ≤ (c + (B : ℤ)) / 2 := Int.ediv_nonneg (by omega) (by omega)
      have h1 : (((c + (B : ℤ)) / 2).toNat : ℤ) = (c + (B : ℤ)) / 2 :=
        Int.toNat_of_nonneg hnn
      have hdiv := Int.mul_ediv_add_emod (c + (B : ℤ)) 2
      have hmod : (c + (B : ℤ)) % 2 = 0 := by omega
      omega

lemma card_parityRange (B : ℕ) : (parityRange B).card = B + 1 := by
  rw [parityRange, Finset.card_image_of_injective _ (fun i j h => by omega), Finset.card_range]

lemma neg_mem_parityRange {B : ℕ} {c : ℤ} (hc : c ∈ parityRange B) : -c ∈ parityRange B := by
  rw [mem_parityRange_iff] at hc ⊢
  omega

lemma disjoint_parityRange {a e : ℕ} (hpar : a % 2 ≠ e % 2) :
    Disjoint (parityRange a) (parityRange e) := by
  rw [Finset.disjoint_left]
  intro c ha he
  rw [mem_parityRange_iff] at ha he
  omega

/-- The 4-parameter knight-lattice projective point set `X(a, e, b, m)`. -/
def knightSet (a e b m : ℕ) : Finset Pt :=
  ((parityRange a ∪ parityRange e).image (fun c => (1, 0, c))) ∪
  ((parityRange a ∪ parityRange e).image (fun c => (0, 1, c))) ∪
  ((parityRange b).image (fun c => (1, 1, c))) ∪
  ((parityRange b).image (fun c => (1, -1, c))) ∪
  ((parityRange m).image (fun c => (1, 2, c))) ∪
  ((parityRange m).image (fun c => (1, -2, c))) ∪
  ((parityRange m).image (fun c => (2, 1, c))) ∪
  ((parityRange m).image (fun c => (2, -1, c))) ∪
  {(0, 0, 1)}

/-- Family A of `deficit-5/2 families`: `(9s + 7, 3s + 2, 8s + 6, 5s + 3)` (`n = 60s + 53`). -/
def familyA (s : ℕ) : Finset Pt :=
  knightSet (9 * s + 7) (3 * s + 2) (8 * s + 6) (5 * s + 3)

/-- Family B of `deficit-5/2 families`: `(9s + 9, 3s + 2, 8s + 8, 5s + 5)` (`n = 60s + 69`). -/
def familyB (s : ℕ) : Finset Pt :=
  knightSet (9 * s + 9) (3 * s + 2) (8 * s + 8) (5 * s + 5)

lemma mem_knightSet_iff {a e b m : ℕ} {p : Pt} :
    p ∈ knightSet a e b m ↔
      (∃ c ∈ parityRange a ∪ parityRange e, p = (1, 0, c)) ∨
      (∃ c ∈ parityRange a ∪ parityRange e, p = (0, 1, c)) ∨
      (∃ c ∈ parityRange b, p = (1, 1, c)) ∨
      (∃ c ∈ parityRange b, p = (1, -1, c)) ∨
      (∃ c ∈ parityRange m, p = (1, 2, c)) ∨
      (∃ c ∈ parityRange m, p = (1, -2, c)) ∨
      (∃ c ∈ parityRange m, p = (2, 1, c)) ∨
      (∃ c ∈ parityRange m, p = (2, -1, c)) ∨
      p = (0, 0, 1) := by
  simp only [knightSet, Finset.mem_union, Finset.mem_image, Finset.mem_singleton, or_assoc]
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
            ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl)
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
            ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl)
    · exact Or.inl ⟨c, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

/-! ### Exact Cardinality, `Proper`, and `NonCollinear` -/

private lemma card_dir_image (u v : ℤ) (S : Finset ℤ) :
    (S.image (fun c => ((u, v, c) : Pt))).card = S.card :=
  Finset.card_image_of_injective S (fun _ _ h => by simp at h; exact h)

theorem knightSet_card {a e b m : ℕ} (hpar : a % 2 ≠ e % 2) :
    (knightSet a e b m).card = 2 * a + 2 * e + 2 * b + 4 * m + 11 := by
  let S1 := (parityRange a ∪ parityRange e).image (fun c => ((1, 0, c) : Pt))
  let S2 := (parityRange a ∪ parityRange e).image (fun c => ((0, 1, c) : Pt))
  let S3 := (parityRange b).image (fun c => ((1, 1, c) : Pt))
  let S4 := (parityRange b).image (fun c => ((1, -1, c) : Pt))
  let S5 := (parityRange m).image (fun c => ((1, 2, c) : Pt))
  let S6 := (parityRange m).image (fun c => ((1, -2, c) : Pt))
  let S7 := (parityRange m).image (fun c => ((2, 1, c) : Pt))
  let S8 := (parityRange m).image (fun c => ((2, -1, c) : Pt))
  let S9 : Finset Pt := {(0, 0, 1)}
  have hdisj : ∀ (A B : Finset Pt) (P : Pt → Prop),
      (∀ p ∈ A, P p) → (∀ p ∈ B, ¬ P p) → Disjoint A B := by
    intro A B P hA hB
    rw [Finset.disjoint_left]
    intro p hpA hpB
    exact hB p hpB (hA p hpA)
  have d12 : Disjoint S1 S2 := hdisj S1 S2 (fun p => p.1 = 1 ∧ p.2.1 = 0)
    (by intro p hp; simp only [S1, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
    (by intro p hp; simp only [S2, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d12_3 : Disjoint (S1 ∪ S2) S3 := hdisj _ S3 (fun p => p.1 ≠ 1 ∨ p.2.1 ≠ 1)
    (by intro p hp; simp only [S1, S2, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S3, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d123_4 : Disjoint (S1 ∪ S2 ∪ S3) S4 := hdisj _ S4 (fun p => p.2.1 ≠ -1)
    (by intro p hp; simp only [S1, S2, S3, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S4, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d1234_5 : Disjoint (S1 ∪ S2 ∪ S3 ∪ S4) S5 := hdisj _ S5 (fun p => p.2.1 ≠ 2)
    (by intro p hp; simp only [S1, S2, S3, S4, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S5, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d12345_6 : Disjoint (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5) S6 := hdisj _ S6 (fun p => p.2.1 ≠ -2)
    (by intro p hp; simp only [S1, S2, S3, S4, S5, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S6, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d123456_7 : Disjoint (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6) S7 := hdisj _ S7 (fun p => p.1 ≠ 2)
    (by intro p hp; simp only [S1, S2, S3, S4, S5, S6, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) |
          ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S7, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d1234567_8 : Disjoint (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7) S8 :=
    hdisj _ S8 (fun p => p.1 ≠ 2 ∨ p.2.1 ≠ -1)
    (by intro p hp; simp only [S1, S2, S3, S4, S5, S6, S7, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with (((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) |
          ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S8, Finset.mem_image] at hp; rcases hp with ⟨_, _, rfl⟩; simp)
  have d12345678_9 : Disjoint (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8) S9 :=
    hdisj _ S9 (fun p => p.1 ≠ 0 ∨ p.2.1 ≠ 0)
    (by intro p hp
        simp only [S1, S2, S3, S4, S5, S6, S7, S8, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with ((((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) |
          ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> simp)
    (by intro p hp; simp only [S9, Finset.mem_singleton] at hp; subst hp; simp)
  have hae : (parityRange a ∪ parityRange e).card = a + e + 2 := by
    rw [Finset.card_union_of_disjoint (disjoint_parityRange hpar), card_parityRange, card_parityRange]
    omega
  change (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8 ∪ S9).card = _
  rw [Finset.card_union_of_disjoint d12345678_9,
      Finset.card_union_of_disjoint d1234567_8,
      Finset.card_union_of_disjoint d123456_7,
      Finset.card_union_of_disjoint d12345_6,
      Finset.card_union_of_disjoint d1234_5,
      Finset.card_union_of_disjoint d123_4,
      Finset.card_union_of_disjoint d12_3,
      Finset.card_union_of_disjoint d12]
  have c1 : S1.card = a + e + 2 := (card_dir_image 1 0 _).trans hae
  have c2 : S2.card = a + e + 2 := (card_dir_image 0 1 _).trans hae
  have c3 : S3.card = b + 1 := (card_dir_image 1 1 _).trans (card_parityRange b)
  have c4 : S4.card = b + 1 := (card_dir_image 1 (-1) _).trans (card_parityRange b)
  have c5 : S5.card = m + 1 := (card_dir_image 1 2 _).trans (card_parityRange m)
  have c6 : S6.card = m + 1 := (card_dir_image 1 (-2) _).trans (card_parityRange m)
  have c7 : S7.card = m + 1 := (card_dir_image 2 1 _).trans (card_parityRange m)
  have c8 : S8.card = m + 1 := (card_dir_image 2 (-1) _).trans (card_parityRange m)
  have c9 : S9.card = 1 := Finset.card_singleton _
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9]
  omega

theorem familyA_card (s : ℕ) : (familyA s).card = 60 * s + 53 := by
  unfold familyA
  rw [knightSet_card (by omega)]
  omega

theorem familyB_card (s : ℕ) : (familyB s).card = 60 * s + 69 := by
  unfold familyB
  rw [knightSet_card (by omega)]
  omega

theorem knightSet_proper (a e b m : ℕ) : Proper (knightSet a e b m) := by
  constructor
  · intro p hp
    rcases mem_knightSet_iff.mp hp with
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;>
    simp [Nonzero]
  · intro p hp q hq hs
    rcases hs with ⟨u, v, hu, hv, hx, hy, hz⟩
    rcases mem_knightSet_iff.mp hp with
      ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ |
      ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | ⟨c₁, _, rfl⟩ | rfl <;>
    rcases mem_knightSet_iff.mp hq with
      ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ |
      ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | ⟨c₂, _, rfl⟩ | rfl <;>
    simp only at hx hy hz <;>
    first
    | rfl
    | (exfalso; omega)
    | (have huv : u = v := by omega
       subst huv
       have hc : c₁ = c₂ := by
         have : u * (c₁ - c₂) = 0 := by linear_combination hz
         have h0 := (mul_eq_zero.mp this).resolve_left hu
         omega
       subst hc; rfl)

theorem knightSet_nonCollinear (a e b m : ℕ) : NonCollinear (knightSet a e b m) := by
  have ha : (a : ℤ) ∈ parityRange a := mem_parityRange_iff.mpr (by omega)
  refine ⟨(1, 0, (a : ℤ)), ?_, (0, 1, (a : ℤ)), ?_, (0, 0, 1), ?_, ?_⟩
  · exact mem_knightSet_iff.mpr (Or.inl ⟨(a : ℤ), Finset.mem_union_left _ ha, rfl⟩)
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨(a : ℤ), Finset.mem_union_left _ ha, rfl⟩))
  · exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · unfold det; ring_nf; omega

/-! ### `D_4 × {±1}` Coordinate Symmetries on `knightSet` -/

private lemma det_eq_zero_of_signed {T S : Pt → Pt}
    (hS : ∀ x y z : Pt, det (S x) (S y) (S z) = 0 ↔ det x y z = 0)
    (hsign : ∀ p : Pt, T p = S p ∨ T p = (-(S p).1, -(S p).2.1, -(S p).2.2)) :
    ∀ x y z : Pt, det (T x) (T y) (T z) = 0 ↔ det x y z = 0 := by
  intro x y z
  have hneg1 : ∀ p q r : Pt, det (-p.1, -p.2.1, -p.2.2) q r = -det p q r := by
    intro p q r; unfold det; ring
  have hneg2 : ∀ p q r : Pt, det p (-q.1, -q.2.1, -q.2.2) r = -det p q r := by
    intro p q r; unfold det; ring
  have hneg3 : ∀ p q r : Pt, det p q (-r.1, -r.2.1, -r.2.2) = -det p q r := by
    intro p q r; unfold det; ring
  rcases hsign x with hx | hx <;> rcases hsign y with hy | hy <;> rcases hsign z with hz | hz <;>
    rw [hx, hy, hz] <;> simp only [hneg1, hneg2, hneg3, neg_eq_zero, hS]

/-- Symmetry 1: negate `z` on all 8 directions, fixing `(0, 0, 1)`. -/
def symZ (p : Pt) : Pt :=
  if p = (0, 0, 1) then (0, 0, 1) else negZ p

/-- Symmetry 2: reflect `y ↦ -y`, keeping canonical leading signs on `knightSet`. -/
def symY (p : Pt) : Pt :=
  if p.1 = 0 ∧ p.2.1 = 1 then (0, 1, -p.2.2) else negY p

/-- Symmetry 3: swap `(x, y) ↦ (y, x)`, keeping canonical leading signs on `knightSet`. -/
def symXY (p : Pt) : Pt :=
  if p.1 = 1 ∧ p.2.1 = -1 then (1, -1, -p.2.2)
  else if p.1 = 1 ∧ p.2.1 = -2 then (2, -1, -p.2.2)
  else if p.1 = 2 ∧ p.2.1 = -1 then (1, -2, -p.2.2)
  else swapXY p

lemma projLineCount_symZ {a e b m : ℕ} {p : Pt} (hp : p ∈ knightSet a e b m) :
    projLineCount (knightSet a e b m) (symZ p) = projLineCount (knightSet a e b m) p := by
  refine projLineCount_eq_of_det_equiv (knightSet_proper a e b m) hp symZ symZ ?_ ?_ ?_ ?_ ?_
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
  · intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ |
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl <;>
    simp [symZ, negZ]
  · refine det_eq_zero_of_signed (S := negZ)
      (fun x y z => by rw [det_negZ, neg_eq_zero]) (fun q => ?_)
    by_cases h : q = (0, 0, 1)
    · subst h; right; simp [symZ, negZ]
    · left; simp [symZ, h]

lemma projLineCount_symY {a e b m : ℕ} {p : Pt} (hp : p ∈ knightSet a e b m) :
    projLineCount (knightSet a e b m) (symY p) = projLineCount (knightSet a e b m) p := by
  have hmem : ∀ q ∈ knightSet a e b m, symY q ∈ knightSet a e b m := by
    intro q hq
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
  have hinvol : ∀ q ∈ knightSet a e b m, symY (symY q) = q := by
    intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ |
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl <;>
    simp [symY, negY]
  refine projLineCount_eq_of_det_equiv (knightSet_proper a e b m) hp symY symY
    hmem hmem hinvol hinvol ?_
  refine det_eq_zero_of_signed (S := negY)
    (fun x y z => by rw [det_negY, neg_eq_zero]) (fun q => ?_)
  by_cases h : q.1 = 0 ∧ q.2.1 = 1
  · right; rcases q with ⟨x, y, z⟩; simp only at h; rcases h with ⟨rfl, rfl⟩; simp [symY, negY]
  · left; simp [symY, h]

lemma projLineCount_symXY {a e b m : ℕ} {p : Pt} (hp : p ∈ knightSet a e b m) :
    projLineCount (knightSet a e b m) (symXY p) = projLineCount (knightSet a e b m) p := by
  have hmem : ∀ q ∈ knightSet a e b m, symXY q ∈ knightSet a e b m := by
    intro q hq
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
  have hinvol : ∀ q ∈ knightSet a e b m, symXY (symXY q) = q := by
    intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ |
      ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ | rfl <;>
    simp [symXY, swapXY]
  refine projLineCount_eq_of_det_equiv (knightSet_proper a e b m) hp symXY symXY
    hmem hmem hinvol hinvol ?_
  refine det_eq_zero_of_signed (S := swapXY)
    (fun x y z => by rw [det_swapXY, neg_eq_zero]) (fun q => ?_)
  rcases q with ⟨x, y, z⟩
  by_cases h1 : x = 1 ∧ y = -1
  · right; rcases h1 with ⟨rfl, rfl⟩; simp [symXY, swapXY]
  · by_cases h2 : x = 1 ∧ y = -2
    · right; rcases h2 with ⟨rfl, rfl⟩; simp [symXY, swapXY]
    · by_cases h3 : x = 2 ∧ y = -1
      · right; rcases h3 with ⟨rfl, rfl⟩; simp [symXY, swapXY]
      · left; simp [symXY, h1, h2, h3]

/-- The origin `(0, 0, 1)` lies on at most `8` spanned lines of `knightSet a e b m`. -/
theorem knightSet_lineCount_origin (a e b m : ℕ) :
    projLineCount (knightSet a e b m) (0, 0, 1) ≤ 8 := by
  have hp : (0, 0, 1) ∈ knightSet a e b m :=
    mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  let L : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (1, 1), (1, -1), (1, 2), (1, -2), (2, 1), (2, -1)}
  refine projLineCount_le_of_label (knightSet_proper a e b m) hp (fun q => (q.1, q.2.1)) L ?_ ?_ ?_
  · have hcard : L.card = 8 := by decide
    omega
  · intro q hq
    have hqne : q ≠ (0, 0, 1) := (Finset.mem_erase.mp hq).1
    rcases mem_knightSet_iff.mp (Finset.mem_of_mem_erase hq) with
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl
    · simp [L]
    · simp [L]
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

/-! ### The 4 Parity-Constant Branches and 16 Kernel-Verified Hull Certificates -/

/-- The 10 affine pencil classes of a knight-lattice branch. -/
def knightPencils (a1 a0 e1 e0 b1 b0 m1 m0 : ℕ) (pa pe pm : ℤ) : List Pencil :=
  [ ⟨1, 0, pa, a1, a0⟩, ⟨1, 0, pe, e1, e0⟩,
    ⟨0, 1, pa, a1, a0⟩, ⟨0, 1, pe, e1, e0⟩,
    ⟨1, 1, 0, b1, b0⟩,  ⟨1, -1, 0, b1, b0⟩,
    ⟨1, -2, pm, m1, m0⟩, ⟨1, 2, pm, m1, m0⟩,
    ⟨2, -1, pm, m1, m0⟩, ⟨2, 1, pm, m1, m0⟩ ]

/-- Non-parallel pencils relative to base direction `(1, q0)`. -/
def nonParallel (q0 : ℤ) (ps : List Pencil) : List Pencil :=
  ps.filter (fun P => P.q - q0 * P.p != 0)

lemma knightSet_covered_by_pencils {a1 a0 e1 e0 b1 b0 m1 m0 t : ℕ} {pa pe pm q0 : ℤ}
    (ha_par : ((a1 * t + a0 : ℕ) : ℤ) % 2 = pa % 2)
    (he_par : ((e1 * t + e0 : ℕ) : ℤ) % 2 = pe % 2)
    (hb_par : ((b1 * t + b0 : ℕ) : ℤ) % 2 = 0)
    (hm_par : ((m1 * t + m0 : ℕ) : ℤ) % 2 = pm % 2) :
    ∀ x ∈ knightSet (a1 * t + a0) (e1 * t + e0) (b1 * t + b0) (m1 * t + m0),
      x.2.1 - q0 * x.1 = 0 ∨
      ∃ P ∈ nonParallel q0 (knightPencils a1 a0 e1 e0 b1 b0 m1 m0 pa pe pm), P.Mem t x := by
  intro x hx
  by_cases hD : x.2.1 - q0 * x.1 = 0
  · exact Or.inl hD
  · right
    have hD_bool : (x.2.1 - q0 * x.1 != 0) = true := bne_iff_ne.mpr hD
    rcases mem_knightSet_iff.mp hx with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
    · rcases Finset.mem_union.mp hc with hca | hce
      · rw [mem_parityRange_iff] at hca
        refine ⟨⟨1, 0, pa, a1, a0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
          rfl, rfl, hca.1, hca.2.1, hca.2.2.trans ha_par⟩
      · rw [mem_parityRange_iff] at hce
        refine ⟨⟨1, 0, pe, e1, e0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
          rfl, rfl, hce.1, hce.2.1, hce.2.2.trans he_par⟩
    · rcases Finset.mem_union.mp hc with hca | hce
      · rw [mem_parityRange_iff] at hca
        refine ⟨⟨0, 1, pa, a1, a0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
          rfl, rfl, hca.1, hca.2.1, hca.2.2.trans ha_par⟩
      · rw [mem_parityRange_iff] at hce
        refine ⟨⟨0, 1, pe, e1, e0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
          rfl, rfl, hce.1, hce.2.1, hce.2.2.trans he_par⟩
    · rw [mem_parityRange_iff] at hc
      refine ⟨⟨1, 1, 0, b1, b0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
        rfl, rfl, hc.1, hc.2.1, by rw [hc.2.2, hb_par]; rfl⟩
    · rw [mem_parityRange_iff] at hc
      refine ⟨⟨1, -1, 0, b1, b0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
        rfl, rfl, hc.1, hc.2.1, by rw [hc.2.2, hb_par]; rfl⟩
    · rw [mem_parityRange_iff] at hc
      refine ⟨⟨1, 2, pm, m1, m0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
        rfl, rfl, hc.1, hc.2.1, hc.2.2.trans hm_par⟩
    · rw [mem_parityRange_iff] at hc
      refine ⟨⟨1, -2, pm, m1, m0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
        rfl, rfl, hc.1, hc.2.1, hc.2.2.trans hm_par⟩
    · rw [mem_parityRange_iff] at hc
      refine ⟨⟨2, 1, pm, m1, m0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
        rfl, rfl, hc.1, hc.2.1, hc.2.2.trans hm_par⟩
    · rw [mem_parityRange_iff] at hc
      refine ⟨⟨2, -1, pm, m1, m0⟩, List.mem_filter.mpr ⟨by simp [knightPencils], hD_bool⟩,
        rfl, rfl, hc.1, hc.2.1, hc.2.2.trans hm_par⟩
    · simp at hD

/-- Branch 0: Family A at even `s = 2t`. -/
def branch0Pencils : List Pencil := knightPencils 18 7 6 2 16 6 10 3 1 0 1
/-- Branch 1: Family B at even `s = 2t`. -/
def branch1Pencils : List Pencil := knightPencils 18 9 6 2 16 8 10 5 1 0 1
/-- Branch 2: Family A at odd `s = 2t + 1`. -/
def branch2Pencils : List Pencil := knightPencils 18 16 6 5 16 14 10 8 0 1 0
/-- Branch 3: Family B at odd `s = 2t + 1`. -/
def branch3Pencils : List Pencil := knightPencils 18 18 6 5 16 16 10 10 0 1 0

/-- Helper combining 6 contiguous `checkC0Range` chunks of size 10 into a full `N2` (`Qc = 120`) certificate. -/
private lemma cert_N2_of_6chunks {ps : List Pencil} {rho0 m1 m0 N1 N0 : ℕ}
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

-- Kernel-verified certificates for Branch 0 (Family A, s = 2t: bound 60t + 24 = 1 + 60t + 23)
theorem cert_b0_Xa : certifyTarget 0 2 (nonParallel 0 branch0Pencils) 1 18 7 4 2 60 23 = true := by decide
theorem cert_b0_Xe : certifyTarget 0 2 (nonParallel 0 branch0Pencils) 0 6 2 4 2 60 23 = true := by decide
theorem cert_b0_S  : certifyTarget 1 6 (nonParallel 1 branch0Pencils) 0 16 6 12 3 60 23 = true := by decide
private theorem cert_b0_N2_h : certifyHeader 2 60 (nonParallel 2 branch0Pencils) 1 10 3 120 12 = true := by decide
private theorem cert_b0_N2_0 : checkC0Range 120 ((nonParallel 2 branch0Pencils).map (Pencil.toAff 2 60)) 10 3 120 12 60 23 1 1 0 10 = true := by decide
private theorem cert_b0_N2_1 : checkC0Range 120 ((nonParallel 2 branch0Pencils).map (Pencil.toAff 2 60)) 10 3 120 12 60 23 1 1 10 10 = true := by decide
private theorem cert_b0_N2_2 : checkC0Range 120 ((nonParallel 2 branch0Pencils).map (Pencil.toAff 2 60)) 10 3 120 12 60 23 1 1 20 10 = true := by decide
private theorem cert_b0_N2_3 : checkC0Range 120 ((nonParallel 2 branch0Pencils).map (Pencil.toAff 2 60)) 10 3 120 12 60 23 1 1 30 10 = true := by decide
private theorem cert_b0_N2_4 : checkC0Range 120 ((nonParallel 2 branch0Pencils).map (Pencil.toAff 2 60)) 10 3 120 12 60 23 1 1 40 10 = true := by decide
private theorem cert_b0_N2_5 : checkC0Range 120 ((nonParallel 2 branch0Pencils).map (Pencil.toAff 2 60)) 10 3 120 12 60 23 1 1 50 10 = true := by decide
theorem cert_b0_N2 : certifyTarget 2 60 (nonParallel 2 branch0Pencils) 1 10 3 120 12 60 23 = true :=
  cert_N2_of_6chunks cert_b0_N2_h cert_b0_N2_0 cert_b0_N2_1 cert_b0_N2_2 cert_b0_N2_3 cert_b0_N2_4 cert_b0_N2_5

-- Kernel-verified certificates for Branch 1 (Family B, s = 2t: bound 60t + 32 = 1 + 60t + 31)
theorem cert_b1_Xa : certifyTarget 0 2 (nonParallel 0 branch1Pencils) 1 18 9 4 2 60 31 = true := by decide
theorem cert_b1_Xe : certifyTarget 0 2 (nonParallel 0 branch1Pencils) 0 6 2 4 2 60 31 = true := by decide
theorem cert_b1_S  : certifyTarget 1 6 (nonParallel 1 branch1Pencils) 0 16 8 12 3 60 31 = true := by decide
private theorem cert_b1_N2_h : certifyHeader 2 60 (nonParallel 2 branch1Pencils) 1 10 5 120 12 = true := by decide
private theorem cert_b1_N2_0 : checkC0Range 120 ((nonParallel 2 branch1Pencils).map (Pencil.toAff 2 60)) 10 5 120 12 60 31 1 1 0 10 = true := by decide
private theorem cert_b1_N2_1 : checkC0Range 120 ((nonParallel 2 branch1Pencils).map (Pencil.toAff 2 60)) 10 5 120 12 60 31 1 1 10 10 = true := by decide
private theorem cert_b1_N2_2 : checkC0Range 120 ((nonParallel 2 branch1Pencils).map (Pencil.toAff 2 60)) 10 5 120 12 60 31 1 1 20 10 = true := by decide
private theorem cert_b1_N2_3 : checkC0Range 120 ((nonParallel 2 branch1Pencils).map (Pencil.toAff 2 60)) 10 5 120 12 60 31 1 1 30 10 = true := by decide
private theorem cert_b1_N2_4 : checkC0Range 120 ((nonParallel 2 branch1Pencils).map (Pencil.toAff 2 60)) 10 5 120 12 60 31 1 1 40 10 = true := by decide
private theorem cert_b1_N2_5 : checkC0Range 120 ((nonParallel 2 branch1Pencils).map (Pencil.toAff 2 60)) 10 5 120 12 60 31 1 1 50 10 = true := by decide
theorem cert_b1_N2 : certifyTarget 2 60 (nonParallel 2 branch1Pencils) 1 10 5 120 12 60 31 = true :=
  cert_N2_of_6chunks cert_b1_N2_h cert_b1_N2_0 cert_b1_N2_1 cert_b1_N2_2 cert_b1_N2_3 cert_b1_N2_4 cert_b1_N2_5

-- Kernel-verified certificates for Branch 2 (Family A, s = 2t + 1: bound 60t + 54 = 1 + 60t + 53)
theorem cert_b2_Xa : certifyTarget 0 2 (nonParallel 0 branch2Pencils) 0 18 16 4 2 60 53 = true := by decide
theorem cert_b2_Xe : certifyTarget 0 2 (nonParallel 0 branch2Pencils) 1 6 5 4 2 60 53 = true := by decide
theorem cert_b2_S  : certifyTarget 1 6 (nonParallel 1 branch2Pencils) 0 16 14 12 3 60 53 = true := by decide
private theorem cert_b2_N2_h : certifyHeader 2 60 (nonParallel 2 branch2Pencils) 0 10 8 120 12 = true := by decide
private theorem cert_b2_N2_0 : checkC0Range 120 ((nonParallel 2 branch2Pencils).map (Pencil.toAff 2 60)) 10 8 120 12 60 53 1 0 0 10 = true := by decide
private theorem cert_b2_N2_1 : checkC0Range 120 ((nonParallel 2 branch2Pencils).map (Pencil.toAff 2 60)) 10 8 120 12 60 53 1 0 10 10 = true := by decide
private theorem cert_b2_N2_2 : checkC0Range 120 ((nonParallel 2 branch2Pencils).map (Pencil.toAff 2 60)) 10 8 120 12 60 53 1 0 20 10 = true := by decide
private theorem cert_b2_N2_3 : checkC0Range 120 ((nonParallel 2 branch2Pencils).map (Pencil.toAff 2 60)) 10 8 120 12 60 53 1 0 30 10 = true := by decide
private theorem cert_b2_N2_4 : checkC0Range 120 ((nonParallel 2 branch2Pencils).map (Pencil.toAff 2 60)) 10 8 120 12 60 53 1 0 40 10 = true := by decide
private theorem cert_b2_N2_5 : checkC0Range 120 ((nonParallel 2 branch2Pencils).map (Pencil.toAff 2 60)) 10 8 120 12 60 53 1 0 50 10 = true := by decide
theorem cert_b2_N2 : certifyTarget 2 60 (nonParallel 2 branch2Pencils) 0 10 8 120 12 60 53 = true :=
  cert_N2_of_6chunks cert_b2_N2_h cert_b2_N2_0 cert_b2_N2_1 cert_b2_N2_2 cert_b2_N2_3 cert_b2_N2_4 cert_b2_N2_5

-- Kernel-verified certificates for Branch 3 (Family B, s = 2t + 1: bound 60t + 62 = 1 + 60t + 61)
theorem cert_b3_Xa : certifyTarget 0 2 (nonParallel 0 branch3Pencils) 0 18 18 4 2 60 61 = true := by decide
theorem cert_b3_Xe : certifyTarget 0 2 (nonParallel 0 branch3Pencils) 1 6 5 4 2 60 61 = true := by decide
theorem cert_b3_S  : certifyTarget 1 6 (nonParallel 1 branch3Pencils) 0 16 16 12 3 60 61 = true := by decide
private theorem cert_b3_N2_h : certifyHeader 2 60 (nonParallel 2 branch3Pencils) 0 10 10 120 12 = true := by decide
private theorem cert_b3_N2_0 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 10 120 12 60 61 1 0 0 10 = true := by decide
private theorem cert_b3_N2_1 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 10 120 12 60 61 1 0 10 10 = true := by decide
private theorem cert_b3_N2_2 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 10 120 12 60 61 1 0 20 10 = true := by decide
private theorem cert_b3_N2_3 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 10 120 12 60 61 1 0 30 10 = true := by decide
private theorem cert_b3_N2_4 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 10 120 12 60 61 1 0 40 10 = true := by decide
private theorem cert_b3_N2_5 : checkC0Range 120 ((nonParallel 2 branch3Pencils).map (Pencil.toAff 2 60)) 10 10 120 12 60 61 1 0 50 10 = true := by decide
theorem cert_b3_N2 : certifyTarget 2 60 (nonParallel 2 branch3Pencils) 0 10 10 120 12 60 61 = true :=
  cert_N2_of_6chunks cert_b3_N2_h cert_b3_N2_0 cert_b3_N2_1 cert_b3_N2_2 cert_b3_N2_3 cert_b3_N2_4 cert_b3_N2_5

/-- Generic upper-bound assembly for a branch from its 4 symmetry-class certificates. -/
private theorem knightSet_branch_upper
    {a1 a0 e1 e0 b1 b0 m1 m0 N1 N0 t : ℕ} {pa pe pm : ℕ}
    (hpa : pa < 2) (hpe : pe < 2) (hpm : pm < 2)
    (ha_par : ((a1 * t + a0 : ℕ) : ℤ) % 2 = (pa : ℤ))
    (he_par : ((e1 * t + e0 : ℕ) : ℤ) % 2 = (pe : ℤ))
    (hb_par : ((b1 * t + b0 : ℕ) : ℤ) % 2 = 0)
    (hm_par : ((m1 * t + m0 : ℕ) : ℤ) % 2 = (pm : ℤ))
    (h8 : 8 ≤ 1 + N1 * t + N0)
    (hXa : certifyTarget 0 2
      (nonParallel 0 (knightPencils a1 a0 e1 e0 b1 b0 m1 m0 pa pe pm)) pa a1 a0 4 2 N1 N0 = true)
    (hXe : certifyTarget 0 2
      (nonParallel 0 (knightPencils a1 a0 e1 e0 b1 b0 m1 m0 pa pe pm)) pe e1 e0 4 2 N1 N0 = true)
    (hS  : certifyTarget 1 6
      (nonParallel 1 (knightPencils a1 a0 e1 e0 b1 b0 m1 m0 pa pe pm)) 0 b1 b0 12 3 N1 N0 = true)
    (hN2 : certifyTarget 2 60
      (nonParallel 2 (knightPencils a1 a0 e1 e0 b1 b0 m1 m0 pa pe pm)) pm m1 m0 120 12 N1 N0 = true) :
    ∀ p ∈ knightSet (a1 * t + a0) (e1 * t + e0) (b1 * t + b0) (m1 * t + m0),
      projLineCount (knightSet (a1 * t + a0) (e1 * t + e0) (b1 * t + b0) (m1 * t + m0)) p ≤
        1 + N1 * t + N0 := by
  set X := knightSet (a1 * t + a0) (e1 * t + e0) (b1 * t + b0) (m1 * t + m0)
  have hpa_mod : (pa : ℤ) % 2 = (pa : ℤ) := by omega
  have hpe_mod : (pe : ℤ) % 2 = (pe : ℤ) := by omega
  have hpm_mod : (pm : ℤ) % 2 = (pm : ℤ) := by omega
  have hcov : ∀ q0 : ℤ, ∀ x ∈ X, x.2.1 - q0 * x.1 = 0 ∨
      ∃ P ∈ nonParallel q0 (knightPencils a1 a0 e1 e0 b1 b0 m1 m0 pa pe pm), P.Mem t x :=
    fun q0 => knightSet_covered_by_pencils (ha_par.trans hpa_mod.symm)
      (he_par.trans hpe_mod.symm) hb_par (hm_par.trans hpm_mod.symm)
  -- Helper: reduce c < 0 to c ≥ 0 via symZ
  have hpos_axis : ∀ c ∈ parityRange (a1 * t + a0) ∪ parityRange (e1 * t + e0),
      0 ≤ c → projLineCount X (1, 0, c) ≤ 1 + N1 * t + N0 := by
    intro c hc hc0
    have hp : (1, 0, c) ∈ X := mem_knightSet_iff.mpr (Or.inl ⟨c, hc, rfl⟩)
    rcases Finset.mem_union.mp hc with hca | hce
    · rw [mem_parityRange_iff] at hca
      exact projLineCount_le_of_certifyTarget hXa (knightSet_proper ..) (hcov 0) hp
        hc0 hca.2.1 (hca.2.2.trans ha_par)
    · rw [mem_parityRange_iff] at hce
      exact projLineCount_le_of_certifyTarget hXe (knightSet_proper ..) (hcov 0) hp
        hc0 hce.2.1 (hce.2.2.trans he_par)
  have hall_axis : ∀ c ∈ parityRange (a1 * t + a0) ∪ parityRange (e1 * t + e0),
      projLineCount X (1, 0, c) ≤ 1 + N1 * t + N0 := by
    intro c hc
    by_cases h0 : 0 ≤ c
    · exact hpos_axis c hc h0
    · have hnc : -c ∈ parityRange (a1 * t + a0) ∪ parityRange (e1 * t + e0) := by
        rcases Finset.mem_union.mp hc with h | h
        · exact Finset.mem_union_left _ (neg_mem_parityRange h)
        · exact Finset.mem_union_right _ (neg_mem_parityRange h)
      have hp : (1, 0, c) ∈ X := mem_knightSet_iff.mpr (Or.inl ⟨c, hc, rfl⟩)
      have hsym : symZ (1, 0, c) = (1, 0, -c) := by simp [symZ, negZ]
      rw [← projLineCount_symZ hp, hsym]
      exact hpos_axis (-c) hnc (by omega)
  have hpos_diag : ∀ c ∈ parityRange (b1 * t + b0),
      0 ≤ c → projLineCount X (1, 1, c) ≤ 1 + N1 * t + N0 := by
    intro c hc hc0
    have hp : (1, 1, c) ∈ X := mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
    rw [mem_parityRange_iff] at hc
    exact projLineCount_le_of_certifyTarget hS (knightSet_proper ..) (hcov 1) hp
      hc0 hc.2.1 (hc.2.2.trans hb_par)
  have hall_diag : ∀ c ∈ parityRange (b1 * t + b0),
      projLineCount X (1, 1, c) ≤ 1 + N1 * t + N0 := by
    intro c hc
    by_cases h0 : 0 ≤ c
    · exact hpos_diag c hc h0
    · have hp : (1, 1, c) ∈ X := mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))
      have hsym : symZ (1, 1, c) = (1, 1, -c) := by simp [symZ, negZ]
      rw [← projLineCount_symZ hp, hsym]
      exact hpos_diag (-c) (neg_mem_parityRange hc) (by omega)
  have hpos_kn : ∀ c ∈ parityRange (m1 * t + m0),
      0 ≤ c → projLineCount X (1, 2, c) ≤ 1 + N1 * t + N0 := by
    intro c hc hc0
    have hp : (1, 2, c) ∈ X :=
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
    rw [mem_parityRange_iff] at hc
    exact projLineCount_le_of_certifyTarget hN2 (knightSet_proper ..) (hcov 2) hp
      hc0 hc.2.1 (hc.2.2.trans hm_par)
  have hall_kn : ∀ c ∈ parityRange (m1 * t + m0),
      projLineCount X (1, 2, c) ≤ 1 + N1 * t + N0 := by
    intro c hc
    by_cases h0 : 0 ≤ c
    · exact hpos_kn c hc h0
    · have hp : (1, 2, c) ∈ X :=
        mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))
      have hsym : symZ (1, 2, c) = (1, 2, -c) := by simp [symZ, negZ]
      rw [← projLineCount_symZ hp, hsym]
      exact hpos_kn (-c) (neg_mem_parityRange hc) (by omega)
  intro p hp
  rcases mem_knightSet_iff.mp hp with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ |
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | rfl
  · exact hall_axis c hc
  · have hsym : symXY (0, 1, c) = (1, 0, c) := by simp [symXY, swapXY]
    rw [← projLineCount_symXY hp, hsym]
    exact hall_axis c hc
  · exact hall_diag c hc
  · have hsym : symY (1, -1, c) = (1, 1, c) := by simp [symY, negY]
    rw [← projLineCount_symY hp, hsym]
    exact hall_diag c hc
  · exact hall_kn c hc
  · have hsym : symY (1, -2, c) = (1, 2, c) := by simp [symY, negY]
    rw [← projLineCount_symY hp, hsym]
    exact hall_kn c hc
  · have hsym : symXY (2, 1, c) = (1, 2, c) := by simp [symXY, swapXY]
    rw [← projLineCount_symXY hp, hsym]
    exact hall_kn c hc
  · have hsym1 : symY (2, -1, c) = (2, 1, c) := by simp [symY, negY]
    have hp1 : (2, 1, c) ∈ X :=
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)))))))
    have hsym2 : symXY (2, 1, c) = (1, 2, c) := by simp [symXY, swapXY]
    rw [← projLineCount_symY hp, hsym1, ← projLineCount_symXY hp1, hsym2]
    exact hall_kn c hc
  · exact (knightSet_lineCount_origin ..).trans h8

/-- **Upper Bound for Family A (`deficit-5/2 families`)**: for every `s ≥ 0` and every `p ∈ familyA s`,
`projLineCount (familyA s) p ≤ 30 * s + 24`. -/
theorem familyA_lineCount_le (s : ℕ) :
    ∀ p ∈ familyA s, projLineCount (familyA s) p ≤ 30 * s + 24 := by
  rcases Nat.even_or_odd s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have heq : familyA (t + t) = knightSet (18 * t + 7) (6 * t + 2) (16 * t + 6) (10 * t + 3) := by
      unfold familyA; congr 1 <;> omega
    have hbd : 30 * (t + t) + 24 = 1 + 60 * t + 23 := by omega
    rw [heq, hbd]
    exact knightSet_branch_upper (pa := 1) (pe := 0) (pm := 1)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      cert_b0_Xa cert_b0_Xe cert_b0_S cert_b0_N2
  · have heq : familyA (2 * t + 1) = knightSet (18 * t + 16) (6 * t + 5) (16 * t + 14) (10 * t + 8) := by
      unfold familyA; congr 1 <;> omega
    have hbd : 30 * (2 * t + 1) + 24 = 1 + 60 * t + 53 := by omega
    rw [heq, hbd]
    exact knightSet_branch_upper (pa := 0) (pe := 1) (pm := 0)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      cert_b2_Xa cert_b2_Xe cert_b2_S cert_b2_N2

/-- **Upper Bound for Family B (`deficit-5/2 families`)**: for every `s ≥ 0` and every `p ∈ familyB s`,
`projLineCount (familyB s) p ≤ 30 * s + 32`. -/
theorem familyB_lineCount_le (s : ℕ) :
    ∀ p ∈ familyB s, projLineCount (familyB s) p ≤ 30 * s + 32 := by
  rcases Nat.even_or_odd s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have heq : familyB (t + t) = knightSet (18 * t + 9) (6 * t + 2) (16 * t + 8) (10 * t + 5) := by
      unfold familyB; congr 1 <;> omega
    have hbd : 30 * (t + t) + 32 = 1 + 60 * t + 31 := by omega
    rw [heq, hbd]
    exact knightSet_branch_upper (pa := 1) (pe := 0) (pm := 1)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      cert_b1_Xa cert_b1_Xe cert_b1_S cert_b1_N2
  · have heq : familyB (2 * t + 1) = knightSet (18 * t + 18) (6 * t + 5) (16 * t + 16) (10 * t + 10) := by
      unfold familyB; congr 1 <;> omega
    have hbd : 30 * (2 * t + 1) + 32 = 1 + 60 * t + 61 := by omega
    rw [heq, hbd]
    exact knightSet_branch_upper (pa := 0) (pe := 1) (pm := 0)
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      cert_b3_Xa cert_b3_Xe cert_b3_S cert_b3_N2

/-! ### Exact Tightness Lower Bounds at the Top Axis Point `(1, 0, a)` -/

/-- General lower-bound lemma via `zLabel 0 a 2`: if every `z ∈ Zwit` is realized by some
`q ∈ X.erase (1, 0, a)` (and every point of `X` has `q.2.1 = 0 ∨ q.2.1 ∣ 2`), then
`Zwit.card ≤ projLineCount X (1, 0, a)`. -/
private lemma le_projLineCount_of_zLabel_hits
    {a : ℤ} {X : Finset Pt} (hX : Proper X) (hp : (1, 0, a) ∈ X)
    (hdvd2 : ∀ q ∈ X, q.2.1 = 0 ∨ q.2.1 ∣ (2 : ℤ))
    (Zwit : Finset (Option ℤ))
    (hhit : ∀ z ∈ Zwit, ∃ q ∈ X.erase (1, 0, a), zLabel 0 a 2 q = z) :
    Zwit.card ≤ projLineCount X (1, 0, a) := by
  classical
  let pick : Option ℤ → Pt := fun z =>
    if h : ∃ q ∈ X.erase (1, 0, a), zLabel 0 a 2 q = z then Classical.choose h else (1, 0, a)
  have hpick : ∀ z ∈ Zwit, pick z ∈ X.erase (1, 0, a) ∧ zLabel 0 a 2 (pick z) = z := by
    intro z hz
    have hex := hhit z hz
    have hEq : pick z = Classical.choose hex := by
      dsimp only [pick]; exact dite_eq_left_of_eq_true (eq_true hex)
    rw [hEq]
    exact Classical.choose_spec hex
  have hsep : ∀ z₁ ∈ Zwit, ∀ z₂ ∈ Zwit, z₁ ≠ z₂ → det (1, 0, a) (pick z₁) (pick z₂) ≠ 0 := by
    intro z₁ hz₁ z₂ hz₂ hne hdet
    apply hne
    have hp₁ := hpick z₁ hz₁
    have hp₂ := hpick z₂ hz₂
    set q₁ := pick z₁
    set q₂ := pick z₂
    have hm₁ : q₁ ∈ X := Finset.mem_of_mem_erase hp₁.1
    have hm₂ : q₂ ∈ X := Finset.mem_of_mem_erase hp₂.1
    have hq₁ne : q₁ ≠ (1, 0, a) := (Finset.mem_erase.mp hp₁.1).1
    have hq₂ne : q₂ ≠ (1, 0, a) := (Finset.mem_erase.mp hp₂.1).1
    rw [← hp₁.2, ← hp₂.2]
    rw [det_one_left] at hdet
    simp only [zero_mul, sub_zero] at hdet
    unfold zLabel
    simp only [zero_mul, sub_zero]
    by_cases h1 : q₁.2.1 = 0
    · have h1_nz : q₁.2.2 - a * q₁.1 ≠ 0 := by
        intro h0
        have hsame : SamePt (1, 0, a) q₁ := by
          have hq₁_x : q₁.1 ≠ 0 := by
            intro hx0
            have hz0 : q₁.2.2 = 0 := by rw [hx0, mul_zero, sub_zero] at h0; exact h0
            exact hX.1 q₁ hm₁ (Prod.ext hx0 (Prod.ext h1 hz0))
          refine ⟨q₁.1, 1, hq₁_x, one_ne_zero, by ring, by simp [h1], by linear_combination -h0⟩
        exact hq₁ne (hX.2 (1, 0, a) hp q₁ hm₁ hsame).symm
      have h2 : q₂.2.1 = 0 := by
        have hmul : q₂.2.1 * (q₁.2.2 - a * q₁.1) = 0 := by
          rw [h1, zero_mul, zero_sub, neg_eq_zero] at hdet; exact hdet
        exact (mul_eq_zero.mp hmul).resolve_right h1_nz
      simp [h1, h2]
    · have h2 : q₂.2.1 ≠ 0 := by
        intro h2z
        have h2_nz : q₂.2.2 - a * q₂.1 ≠ 0 := by
          intro h0
          have hsame : SamePt (1, 0, a) q₂ := by
            have hq₂_x : q₂.1 ≠ 0 := by
              intro hx0
              have hz0 : q₂.2.2 = 0 := by rw [hx0, mul_zero, sub_zero] at h0; exact h0
              exact hX.1 q₂ hm₂ (Prod.ext hx0 (Prod.ext h2z hz0))
            refine ⟨q₂.1, 1, hq₂_x, one_ne_zero, by ring, by simp [h2z], by linear_combination -h0⟩
          exact hq₂ne (hX.2 (1, 0, a) hp q₂ hm₂ hsame).symm
        have hmul : q₁.2.1 * (q₂.2.2 - a * q₂.1) = 0 := by
          rw [h2z, zero_mul, sub_zero] at hdet; exact hdet
        exact h1 ((mul_eq_zero.mp hmul).resolve_right h2_nz)
      simp only [h1, h2, ↓reduceIte]
      congr 1
      have hd₁ : q₁.2.1 ∣ (2 : ℤ) := (hdvd2 q₁ hm₁).resolve_left h1
      have hd₂ : q₂.2.1 ∣ (2 : ℤ) := (hdvd2 q₂ hm₂).resolve_left h2
      have hm1 : q₁.2.1 * (((2 : ℕ) : ℤ) * (q₁.2.2 - a * q₁.1) / q₁.2.1) =
          ((2 : ℕ) : ℤ) * (q₁.2.2 - a * q₁.1) :=
        Int.mul_ediv_cancel' (dvd_mul_of_dvd_left hd₁ _)
      have hm2 : q₂.2.1 * (((2 : ℕ) : ℤ) * (q₂.2.2 - a * q₂.1) / q₂.2.1) =
          ((2 : ℕ) : ℤ) * (q₂.2.2 - a * q₂.1) :=
        Int.mul_ediv_cancel' (dvd_mul_of_dvd_left hd₂ _)
      have hscaled : q₁.2.1 * q₂.2.1 *
          ((((2 : ℕ) : ℤ) * (q₂.2.2 - a * q₂.1) / q₂.2.1) -
           (((2 : ℕ) : ℤ) * (q₁.2.2 - a * q₁.1) / q₁.2.1)) = 0 := by
        calc q₁.2.1 * q₂.2.1 *
              ((((2 : ℕ) : ℤ) * (q₂.2.2 - a * q₂.1) / q₂.2.1) -
               (((2 : ℕ) : ℤ) * (q₁.2.2 - a * q₁.1) / q₁.2.1))
            = q₁.2.1 * (q₂.2.1 * (((2 : ℕ) : ℤ) * (q₂.2.2 - a * q₂.1) / q₂.2.1)) -
              q₂.2.1 * (q₁.2.1 * (((2 : ℕ) : ℤ) * (q₁.2.2 - a * q₁.1) / q₁.2.1)) := by ring
          _ = q₁.2.1 * (((2 : ℕ) : ℤ) * (q₂.2.2 - a * q₂.1)) -
              q₂.2.1 * (((2 : ℕ) : ℤ) * (q₁.2.2 - a * q₁.1)) := by rw [hm1, hm2]
          _ = 2 * (q₁.2.1 * (q₂.2.2 - a * q₂.1) - q₂.2.1 * (q₁.2.2 - a * q₁.1)) := by norm_num; ring
          _ = 0 := by rw [hdet]; ring
      have hdiff0 := (mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero h1 h2)
      omega
  have hinj : Set.InjOn (fun z => projLine (1, 0, a) (pick z)) Zwit := by
    intro z₁ hz₁ z₂ hz₂ heq
    by_contra hne
    have hp₁ := hpick z₁ hz₁
    have hp₂ := hpick z₂ hz₂
    have hm₁ : pick z₁ ∈ X := Finset.mem_of_mem_erase hp₁.1
    have hm₂ : pick z₂ ∈ X := Finset.mem_of_mem_erase hp₂.1
    have hns₁ : ¬ SamePt (1, 0, a) (pick z₁) :=
      fun hs => (Finset.mem_erase.mp hp₁.1).1 (hX.2 (1, 0, a) hp (pick z₁) hm₁ hs).symm
    have hns₂ : ¬ SamePt (1, 0, a) (pick z₂) :=
      fun hs => (Finset.mem_erase.mp hp₂.1).1 (hX.2 (1, 0, a) hp (pick z₂) hm₂ hs).symm
    have hdet : det (1, 0, a) (pick z₁) (pick z₂) = 0 :=
      (projLine_eq_iff_det_eq_zero (hX.1 _ hp) (hX.1 _ hm₁) (hX.1 _ hm₂) hns₁ hns₂).mp heq
    exact hsep z₁ hz₁ z₂ hz₂ hne hdet
  refine Finset.card_le_card_of_injOn (fun z => projLine (1, 0, a) (pick z)) ?_ hinj
  intro z hz
  simp only [spannedProjLines, Finset.mem_coe, Finset.mem_image]
  exact ⟨pick z, (hpick z hz).1, rfl⟩

/-- Explicit set of `30s + 23 + 8δ` distinct integer heights `y` (corresponding to `z = 2y`)
realized on lines through `(1, 0, a)` in `knightSet (9s+7+2δ) (3s+2) (8s+6+2δ) (5s+3+2δ)`. -/
private def tightY (s δ : ℕ) : Finset ℤ :=
  let a := 9 * s + 7 + 2 * δ
  let e := 3 * s + 2
  let b := 8 * s + 6 + 2 * δ
  parityRange a ∪ parityRange e ∪
  ((Finset.range (4 * s + 3 + δ)).image (fun (k : ℕ) => -((a : ℤ) + 2 * (k : ℤ) + 2))) ∪
  ((Finset.range (4 * s + 3 + δ)).image (fun (k : ℕ) => (a : ℤ) + 2 * (k : ℤ) + 2)) ∪
  ((Finset.range (3 * s + 2 + δ)).image (fun (k : ℕ) => -((a : ℤ) + (b : ℤ) + 2 * (k : ℤ) + 2))) ∪
  ((Finset.range (3 * s + 2 + δ)).image (fun (k : ℕ) => (a : ℤ) + (b : ℤ) + 2 * (k : ℤ) + 2)) ∪
  ((Finset.range (2 * s + 1 + δ)).image (fun (k : ℕ) => -((e : ℤ) + 2 + 2 * (k : ℤ)))) ∪
  ((Finset.range (2 * s + 1 + δ)).image (fun (k : ℕ) => (e : ℤ) + 2 + 2 * (k : ℤ)))

private lemma tightY_card (s δ : ℕ) : (tightY s δ).card = 30 * s + 23 + 8 * δ := by
  set a := 9 * s + 7 + 2 * δ
  set e := 3 * s + 2
  set b := 8 * s + 6 + 2 * δ
  let HorA : Finset ℤ := parityRange a
  let HorE : Finset ℤ := parityRange e
  let DiagNeg : Finset ℤ := (Finset.range (4 * s + 3 + δ)).image (fun (k : ℕ) => -((a : ℤ) + 2 * (k : ℤ) + 2))
  let DiagPos : Finset ℤ := (Finset.range (4 * s + 3 + δ)).image (fun (k : ℕ) => (a : ℤ) + 2 * (k : ℤ) + 2)
  let Kn2Neg : Finset ℤ := (Finset.range (3 * s + 2 + δ)).image (fun (k : ℕ) => -((a : ℤ) + (b : ℤ) + 2 * (k : ℤ) + 2))
  let Kn2Pos : Finset ℤ := (Finset.range (3 * s + 2 + δ)).image (fun (k : ℕ) => (a : ℤ) + (b : ℤ) + 2 * (k : ℤ) + 2)
  let Kn1Neg : Finset ℤ := (Finset.range (2 * s + 1 + δ)).image (fun (k : ℕ) => -((e : ℤ) + 2 + 2 * (k : ℤ)))
  let Kn1Pos : Finset ℤ := (Finset.range (2 * s + 1 + δ)).image (fun (k : ℕ) => (e : ℤ) + 2 + 2 * (k : ℤ))
  have hmem_HorA : ∀ y ∈ HorA, -(a : ℤ) ≤ y ∧ y ≤ (a : ℤ) ∧ y % 2 = (a : ℤ) % 2 :=
    fun _ hy => mem_parityRange_iff.mp hy
  have hmem_HorE : ∀ y ∈ HorE, -(e : ℤ) ≤ y ∧ y ≤ (e : ℤ) ∧ y % 2 = (e : ℤ) % 2 :=
    fun _ hy => mem_parityRange_iff.mp hy
  have hmem_DN : ∀ y ∈ DiagNeg, -((a : ℤ) + (b : ℤ)) ≤ y ∧ y ≤ -(a : ℤ) - 2 := by
    intro y hy; simp only [DiagNeg, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ⟨k, hk, rfl⟩; omega
  have hmem_DP : ∀ y ∈ DiagPos, (a : ℤ) + 2 ≤ y ∧ y ≤ (a : ℤ) + (b : ℤ) := by
    intro y hy; simp only [DiagPos, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ⟨k, hk, rfl⟩; omega
  have hmem_K2N : ∀ y ∈ Kn2Neg, y ≤ -((a : ℤ) + (b : ℤ)) - 2 := by
    intro y hy; simp only [Kn2Neg, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ⟨k, hk, rfl⟩; omega
  have hmem_K2P : ∀ y ∈ Kn2Pos, (a : ℤ) + (b : ℤ) + 2 ≤ y := by
    intro y hy; simp only [Kn2Pos, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ⟨k, hk, rfl⟩; omega
  have hmem_K1N : ∀ y ∈ Kn1Neg, -(a : ℤ) < y ∧ y ≤ -(e : ℤ) - 2 ∧ y % 2 = (e : ℤ) % 2 := by
    intro y hy; simp only [Kn1Neg, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ⟨k, hk, rfl⟩; omega
  have hmem_K1P : ∀ y ∈ Kn1Pos, (e : ℤ) + 2 ≤ y ∧ y < (a : ℤ) ∧ y % 2 = (e : ℤ) % 2 := by
    intro y hy; simp only [Kn1Pos, Finset.mem_image, Finset.mem_range] at hy
    rcases hy with ⟨k, hk, rfl⟩; omega
  have d1 : Disjoint HorA HorE := disjoint_parityRange (by omega)
  have d2 : Disjoint (HorA ∪ HorE) DiagNeg := by
    rw [Finset.disjoint_left]; intro y h1 h2
    have hDN := hmem_DN y h2
    rcases Finset.mem_union.mp h1 with hA | hE
    · have := hmem_HorA y hA; omega
    · have := hmem_HorE y hE; omega
  have d3 : Disjoint (HorA ∪ HorE ∪ DiagNeg) DiagPos := by
    rw [Finset.disjoint_left]; intro y h1 h2
    have hDP := hmem_DP y h2
    rcases Finset.mem_union.mp h1 with h1' | hDN
    · rcases Finset.mem_union.mp h1' with hA | hE
      · have := hmem_HorA y hA; omega
      · have := hmem_HorE y hE; omega
    · have := hmem_DN y hDN; omega
  have d4 : Disjoint (HorA ∪ HorE ∪ DiagNeg ∪ DiagPos) Kn2Neg := by
    rw [Finset.disjoint_left]; intro y h1 h2
    have hK := hmem_K2N y h2
    rcases Finset.mem_union.mp h1 with h1' | hDP
    · rcases Finset.mem_union.mp h1' with h1'' | hDN
      · rcases Finset.mem_union.mp h1'' with hA | hE
        · have := hmem_HorA y hA; omega
        · have := hmem_HorE y hE; omega
      · have := hmem_DN y hDN; omega
    · have := hmem_DP y hDP; omega
  have d5 : Disjoint (HorA ∪ HorE ∪ DiagNeg ∪ DiagPos ∪ Kn2Neg) Kn2Pos := by
    rw [Finset.disjoint_left]; intro y h1 h2
    have hK := hmem_K2P y h2
    rcases Finset.mem_union.mp h1 with h1' | hK2N
    · rcases Finset.mem_union.mp h1' with h1'' | hDP
      · rcases Finset.mem_union.mp h1'' with h1''' | hDN
        · rcases Finset.mem_union.mp h1''' with hA | hE
          · have := hmem_HorA y hA; omega
          · have := hmem_HorE y hE; omega
        · have := hmem_DN y hDN; omega
      · have := hmem_DP y hDP; omega
    · have := hmem_K2N y hK2N; omega
  have d6 : Disjoint (HorA ∪ HorE ∪ DiagNeg ∪ DiagPos ∪ Kn2Neg ∪ Kn2Pos) Kn1Neg := by
    rw [Finset.disjoint_left]; intro y h1 h2
    have hK := hmem_K1N y h2
    rcases Finset.mem_union.mp h1 with h1' | hK2P
    · rcases Finset.mem_union.mp h1' with h1'' | hK2N
      · rcases Finset.mem_union.mp h1'' with h1''' | hDP
        · rcases Finset.mem_union.mp h1''' with h1'''' | hDN
          · rcases Finset.mem_union.mp h1'''' with hA | hE
            · have := hmem_HorA y hA; omega
            · have := hmem_HorE y hE; omega
          · have := hmem_DN y hDN; omega
        · have := hmem_DP y hDP; omega
      · have := hmem_K2N y hK2N; omega
    · have := hmem_K2P y hK2P; omega
  have d7 : Disjoint (HorA ∪ HorE ∪ DiagNeg ∪ DiagPos ∪ Kn2Neg ∪ Kn2Pos ∪ Kn1Neg) Kn1Pos := by
    rw [Finset.disjoint_left]; intro y h1 h2
    have hK := hmem_K1P y h2
    rcases Finset.mem_union.mp h1 with h1' | hK1N
    · rcases Finset.mem_union.mp h1' with h1'' | hK2P
      · rcases Finset.mem_union.mp h1'' with h1''' | hK2N
        · rcases Finset.mem_union.mp h1''' with h1'''' | hDP
          · rcases Finset.mem_union.mp h1'''' with h1''''' | hDN
            · rcases Finset.mem_union.mp h1''''' with hA | hE
              · have := hmem_HorA y hA; omega
              · have := hmem_HorE y hE; omega
            · have := hmem_DN y hDN; omega
          · have := hmem_DP y hDP; omega
        · have := hmem_K2N y hK2N; omega
      · have := hmem_K2P y hK2P; omega
    · have := hmem_K1N y hK1N; omega
  have cHA : HorA.card = a + 1 := card_parityRange a
  have cHE : HorE.card = e + 1 := card_parityRange e
  have cDN : DiagNeg.card = 4 * s + 3 + δ := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have cDP : DiagPos.card = 4 * s + 3 + δ := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have cK2N : Kn2Neg.card = 3 * s + 2 + δ := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have cK2P : Kn2Pos.card = 3 * s + 2 + δ := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have cK1N : Kn1Neg.card = 2 * s + 1 + δ := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have cK1P : Kn1Pos.card = 2 * s + 1 + δ := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  change (HorA ∪ HorE ∪ DiagNeg ∪ DiagPos ∪ Kn2Neg ∪ Kn2Pos ∪ Kn1Neg ∪ Kn1Pos).card = _
  rw [Finset.card_union_of_disjoint d7, Finset.card_union_of_disjoint d6,
      Finset.card_union_of_disjoint d5, Finset.card_union_of_disjoint d4,
      Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d1,
      cHA, cHE, cDN, cDP, cK2N, cK2P, cK1N, cK1P]
  omega

private lemma tightY_hit (s δ : ℕ) {y : ℤ} (hy : y ∈ tightY s δ) :
    let a := 9 * s + 7 + 2 * δ
    let e := 3 * s + 2
    let b := 8 * s + 6 + 2 * δ
    let m := 5 * s + 3 + 2 * δ
    ∃ q ∈ (knightSet a e b m).erase (1, 0, (a : ℤ)), zLabel 0 (a : ℤ) 2 q = some (2 * y) := by
  intro a e b m
  have hdiv_neg1 : ∀ u : ℤ, u / (-1 : ℤ) = -u := fun u => by omega
  have hdiv_2 : ∀ u : ℤ, (2 * u) / (2 : ℤ) = u := fun u => by omega
  have hdiv_neg2 : ∀ u : ℤ, (2 * u) / (-2 : ℤ) = -u := fun u => by omega
  simp only [tightY, Finset.mem_union] at hy
  rcases hy with ((((((hHA | hHE) | hDN) | hDP) | hK2N) | hK2P) | hK1N) | hK1P
  · refine ⟨(0, 1, y), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨y, Finset.mem_union_left _ hHA, rfl⟩))⟩, ?_⟩
    unfold zLabel; simp
  · refine ⟨(0, 1, y), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨y, Finset.mem_union_right _ hHE, rfl⟩))⟩, ?_⟩
    unfold zLabel; simp
  · simp only [Finset.mem_image, Finset.mem_range] at hDN
    rcases hDN with ⟨k, hk, rfl⟩
    let d : ℤ := -(2 * (k : ℤ) + 2)
    have hd : d ∈ parityRange b := mem_parityRange_iff.mpr (by omega)
    refine ⟨(1, 1, d), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩)))⟩, ?_⟩
    unfold zLabel; simp only [sub_zero, mul_one, one_ne_zero, ↓reduceIte,
      Int.ediv_one, Nat.cast_ofNat, Option.some.injEq]
    dsimp only [d]; ring
  · simp only [Finset.mem_image, Finset.mem_range] at hDP
    rcases hDP with ⟨k, hk, rfl⟩
    let d : ℤ := -(2 * (k : ℤ) + 2)
    have hd : d ∈ parityRange b := mem_parityRange_iff.mpr (by omega)
    refine ⟨(1, -1, d), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩))))⟩, ?_⟩
    unfold zLabel
    simp only [sub_zero, mul_one, Nat.cast_ofNat, Option.some.injEq,
      show (-1 : ℤ) ≠ 0 by omega, ↓reduceIte, hdiv_neg1]
    dsimp only [d]; ring
  · simp only [Finset.mem_image, Finset.mem_range] at hK2N
    rcases hK2N with ⟨k, hk, rfl⟩
    let d : ℤ := (a : ℤ) - (b : ℤ) - 2 * (k : ℤ) - 2
    have hd : d ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
    refine ⟨(2, 1, d), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩)))))))⟩, ?_⟩
    unfold zLabel; simp only [zero_mul, sub_zero, one_ne_zero, ↓reduceIte,
      Int.ediv_one, Nat.cast_ofNat, Option.some.injEq]
    dsimp only [d]; ring
  · simp only [Finset.mem_image, Finset.mem_range] at hK2P
    rcases hK2P with ⟨k, hk, rfl⟩
    let d : ℤ := (a : ℤ) - (b : ℤ) - 2 * (k : ℤ) - 2
    have hd : d ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
    refine ⟨(2, -1, d), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩))))))))⟩, ?_⟩
    unfold zLabel
    simp only [zero_mul, sub_zero, Nat.cast_ofNat, Option.some.injEq,
      show (-1 : ℤ) ≠ 0 by omega, ↓reduceIte, hdiv_neg1]
    dsimp only [d]; ring
  · simp only [Finset.mem_image, Finset.mem_range] at hK1N
    rcases hK1N with ⟨k, hk, rfl⟩
    let d : ℤ := (a : ℤ) - 2 * ((e : ℤ) + 2 + 2 * (k : ℤ))
    have hd : d ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
    refine ⟨(1, 2, d), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩)))))⟩, ?_⟩
    unfold zLabel
    simp only [sub_zero, mul_one, Nat.cast_ofNat, Option.some.injEq,
      show (2 : ℤ) ≠ 0 by omega, ↓reduceIte, hdiv_2]
    dsimp only [d]; ring
  · simp only [Finset.mem_image, Finset.mem_range] at hK1P
    rcases hK1P with ⟨k, hk, rfl⟩
    let d : ℤ := (a : ℤ) - 2 * ((e : ℤ) + 2 + 2 * (k : ℤ))
    have hd : d ∈ parityRange m := mem_parityRange_iff.mpr (by omega)
    refine ⟨(1, -2, d), Finset.mem_erase.mpr ⟨by simp,
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩))))))⟩, ?_⟩
    unfold zLabel
    simp only [sub_zero, mul_one, Nat.cast_ofNat, Option.some.injEq,
      show (-2 : ℤ) ≠ 0 by omega, ↓reduceIte, hdiv_neg2]
    dsimp only [d]; ring

/-- Unified tightness lower bound for both Family A (`δ = 0`) and Family B (`δ = 1`):
parameters `(a, e, b, m) = (9s + 7 + 2δ, 3s + 2, 8s + 6 + 2δ, 5s + 3 + 2δ)` achieve
`projLineCount X (1, 0, a) ≥ 30s + 24 + 8δ`. -/
private theorem knightSet_tight_common (s δ : ℕ) :
    let a := 9 * s + 7 + 2 * δ
    let e := 3 * s + 2
    let b := 8 * s + 6 + 2 * δ
    let m := 5 * s + 3 + 2 * δ
    30 * s + 24 + 8 * δ ≤ projLineCount (knightSet a e b m) (1, 0, (a : ℤ)) := by
  intro a e b m
  set X := knightSet a e b m
  have ha_mem : (a : ℤ) ∈ parityRange a := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, (a : ℤ)) ∈ X :=
    mem_knightSet_iff.mpr (Or.inl ⟨(a : ℤ), Finset.mem_union_left _ ha_mem, rfl⟩)
  have hdvd2 : ∀ q ∈ X, q.2.1 = 0 ∨ q.2.1 ∣ (2 : ℤ) := by
    intro q hq
    rcases mem_knightSet_iff.mp hq with
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
      ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;>
    simp
  let Zwit : Finset (Option ℤ) := insert none ((tightY s δ).image (fun y => some (2 * y)))
  have hZcard : Zwit.card = 30 * s + 24 + 8 * δ := by
    have hnone : none ∉ (tightY s δ).image (fun y => some (2 * y)) := by simp
    rw [Finset.card_insert_of_notMem hnone,
        Finset.card_image_of_injective _ (fun _ _ h => by simp at h; omega), tightY_card s δ]
    omega
  rw [← hZcard]
  refine le_projLineCount_of_zLabel_hits (knightSet_proper a e b m) hp hdvd2 Zwit ?_
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | himg
  · refine ⟨(0, 0, 1), Finset.mem_erase.mpr ⟨by simp, ?_⟩, by simp [zLabel]⟩
    exact mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · rcases Finset.mem_image.mp himg with ⟨y, hy, rfl⟩
    exact tightY_hit s δ hy

/-- **Exact Tightness for Family A**: `(1, 0, 9s + 7)` lies on exactly `30s + 24` lines. -/
theorem familyA_top_lineCount (s : ℕ) :
    projLineCount (familyA s) (1, 0, ((9 * s + 7 : ℕ) : ℤ)) = 30 * s + 24 := by
  have hge := knightSet_tight_common s 0
  have ha : ((9 * s + 7 : ℕ) : ℤ) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 7 : ℕ) : ℤ)) ∈ familyA s :=
    mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  exact le_antisymm (familyA_lineCount_le s _ hp) (by simpa [familyA] using hge)

/-- **Exact Tightness for Family B**: `(1, 0, 9s + 9)` lies on exactly `30s + 32` lines. -/
theorem familyB_top_lineCount (s : ℕ) :
    projLineCount (familyB s) (1, 0, ((9 * s + 9 : ℕ) : ℤ)) = 30 * s + 32 := by
  have hge0 := knightSet_tight_common s 1
  have hge : 30 * s + 32 ≤ projLineCount (familyB s) (1, 0, ((9 * s + 9 : ℕ) : ℤ)) := by
    have h1 : 9 * s + 7 + 2 * 1 = 9 * s + 9 := by omega
    have h2 : 8 * s + 6 + 2 * 1 = 8 * s + 8 := by omega
    have h3 : 5 * s + 3 + 2 * 1 = 5 * s + 5 := by omega
    have h4 : 30 * s + 24 + 8 * 1 = 30 * s + 32 := by omega
    unfold familyB
    simpa only [h1, h2, h3, h4] using hge0
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 9 : ℕ) : ℤ)) ∈ familyB s :=
    mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  exact le_antisymm (familyB_lineCount_le s _ hp) hge

/-! ### Main Euclidean Headline Theorems for `deficit-5/2 families` -/

/-- **Main Euclidean Headline Theorem (`deficit-5/2 families`, Family A)**: for every `s ≥ 0`, there exists
a non-collinear set `P` of `60s + 53` points in `ℝ²` whose maximum spanned line count per
point is **equal to** `30s + 24 = (P.card - 5) / 2` (deficit `5/2`). -/
theorem deficit52_familyA_euclidean (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 53 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 24) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 24) := by
  have ha : ((9 * s + 7 : ℕ) : ℤ) ∈ parityRange (9 * s + 7) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 7 : ℕ) : ℤ)) ∈ familyA s :=
    mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  exact exists_euclidean_set_eq (knightSet_proper ..) (familyA_card s) (knightSet_nonCollinear ..)
    (familyA_lineCount_le s) ⟨_, hp, le_of_eq (familyA_top_lineCount s).symm⟩

/-- **Main Euclidean Headline Theorem (`deficit-5/2 families`, Family B)**: for every `s ≥ 0`, there exists
a non-collinear set `P` of `60s + 69` points in `ℝ²` whose maximum spanned line count per
point is **equal to** `30s + 32 = (P.card - 5) / 2` (deficit `5/2`). -/
theorem deficit52_familyB_euclidean (s : ℕ) :
    ∃ P : Finset (ℝ × ℝ),
      P.card = 60 * s + 69 ∧
      NonCollinearR2 P ∧
      (∀ a ∈ P, lineCountR2 P a ≤ 30 * s + 32) ∧
      (∃ a ∈ P, lineCountR2 P a = 30 * s + 32) := by
  have ha : ((9 * s + 9 : ℕ) : ℤ) ∈ parityRange (9 * s + 9) := mem_parityRange_iff.mpr (by omega)
  have hp : (1, 0, ((9 * s + 9 : ℕ) : ℤ)) ∈ familyB s :=
    mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha, rfl⟩)
  exact exists_euclidean_set_eq (knightSet_proper ..) (familyB_card s) (knightSet_nonCollinear ..)
    (familyB_lineCount_le s) ⟨_, hp, le_of_eq (familyB_top_lineCount s).symm⟩

/-- Grünbaum's (2010) conjectured asymptotic minimum `G(n) = 2 ⌊n / 4⌋`. -/
def grunbaumVal (n : ℕ) : ℕ := 2 * (n / 4)

/-- **Refutation of Grünbaum's (2010) Conjecture** in four residue classes mod 12
(`n ≡ 52, 53, 8, 9 (mod 60)`, i.e. `m = 4, 5, 8, 9`): for every `s ≥ 0`, deleting 0 or 1
points from Family A or Family B gives non-collinear Euclidean sets beating `G(n)` by `2`. -/
theorem deficit52_refutes_grunbaum (s : ℕ) :
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 53 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 52 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 69 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) ∧
    (∃ P : Finset (ℝ × ℝ), P.card = 60 * s + 68 ∧ NonCollinearR2 P ∧
      ∀ a ∈ P, lineCountR2 P a ≤ grunbaumVal P.card - 2) := by
  have hdel : ∀ {a e b m B : ℕ},
      (knightSet a e b m).card = B + 1 →
      (∀ p ∈ knightSet a e b m, projLineCount (knightSet a e b m) p ≤ grunbaumVal B - 2) →
      ∃ P : Finset (ℝ × ℝ), P.card = B ∧ NonCollinearR2 P ∧
        ∀ x ∈ P, lineCountR2 P x ≤ grunbaumVal P.card - 2 := by
    intro a e b m B hcard hbd
    let X' := (knightSet a e b m).erase (1, 1, (b : ℤ))
    have hb_mem : (b : ℤ) ∈ parityRange b := mem_parityRange_iff.mpr (by omega)
    have hq_mem : (1, 1, (b : ℤ)) ∈ knightSet a e b m :=
      mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inl ⟨(b : ℤ), hb_mem, rfl⟩)))
    have hX'_proper : Proper X' :=
      ⟨fun p hp => (knightSet_proper a e b m).1 p (Finset.mem_of_mem_erase hp),
       fun p hp q hq => (knightSet_proper a e b m).2 p (Finset.mem_of_mem_erase hp)
         q (Finset.mem_of_mem_erase hq)⟩
    have hX'_card : X'.card = B := by
      rw [Finset.card_erase_of_mem hq_mem, hcard]; omega
    have hX'_nc : NonCollinear X' := by
      have ha_mem : (a : ℤ) ∈ parityRange a := mem_parityRange_iff.mpr (by omega)
      refine ⟨(1, 0, (a : ℤ)), Finset.mem_erase.mpr ⟨by simp,
          mem_knightSet_iff.mpr (Or.inl ⟨_, Finset.mem_union_left _ ha_mem, rfl⟩)⟩,
        (0, 1, (a : ℤ)), Finset.mem_erase.mpr ⟨by simp,
          mem_knightSet_iff.mpr (Or.inr (Or.inl ⟨_, Finset.mem_union_left _ ha_mem, rfl⟩))⟩,
        (0, 0, 1), Finset.mem_erase.mpr ⟨by simp,
          mem_knightSet_iff.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))⟩,
        by unfold det; ring_nf; omega⟩
    have hX'_bd : ∀ p ∈ X', projLineCount X' p ≤ grunbaumVal B - 2 := fun p hp =>
      (projLineCount_erase_le _ p _).trans (hbd p (Finset.mem_of_mem_erase hp))
    obtain ⟨P, hPc, hPnc, hPbd⟩ := exists_euclidean_set_le hX'_proper hX'_card hX'_nc hX'_bd
    exact ⟨P, hPc, hPnc, fun x hx => by rw [hPc]; exact hPbd x hx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, hPc, hPnc, hPbd, _⟩ := deficit52_familyA_euclidean s
    refine ⟨P, hPc, hPnc, fun x hx => ?_⟩
    have hG : 30 * s + 24 ≤ grunbaumVal P.card - 2 := by rw [hPc]; unfold grunbaumVal; omega
    exact (hPbd x hx).trans hG
  · refine hdel (familyA_card s) (fun p hp => ?_)
    have hG : 30 * s + 24 ≤ grunbaumVal (60 * s + 52) - 2 := by unfold grunbaumVal; omega
    exact (familyA_lineCount_le s p hp).trans hG
  · obtain ⟨P, hPc, hPnc, hPbd, _⟩ := deficit52_familyB_euclidean s
    refine ⟨P, hPc, hPnc, fun x hx => ?_⟩
    have hG : 30 * s + 32 ≤ grunbaumVal P.card - 2 := by rw [hPc]; unfold grunbaumVal; omega
    exact (hPbd x hx).trans hG
  · refine hdel (familyB_card s) (fun p hp => ?_)
    have hG : 30 * s + 32 ≤ grunbaumVal (60 * s + 68) - 2 := by unfold grunbaumVal; omega
    exact (familyB_lineCount_le s p hp).trans hG

end DeficitFiveHalves

end StrongDirac
