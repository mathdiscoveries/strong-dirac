module

public import StrongDirac.Projective
public import Mathlib.Data.Int.Interval

import Mathlib.Tactic

/-!
# Verified Interval-Hull Convexity Certificate Engine (`StrongDirac.HullCert`)

Provides a completely general, 100% unconditional Lean 4 soundness proof for
the interval-hull convexity method used to prove the all-`s` upper bound of
`R17-2-1`:
- For any finite projective point set `X` partitioned into linear pencil classes
  `(p, q, rho, B1, B0)` (plus points parallel to a base point `p0 = (1, q0, c)`),
  the scaled projective coordinate `z(x) = Lam * (x.2.2 - c * x.1) / (x.2.1 - q0 * x.1)`
  classifies lines through `p0` (`det_one_left`).
- Each non-parallel pencil maps into an arithmetic progression of step `mu = 2 * f`
  inside `[lc * c - (ht * t + h0), lc * c + (ht * t + h0)]`.
- Grouping by residue `σ ∈ [0, M)` (`M = 2 * Lam`), the number of distinct
  residues hit is bounded by the hull sum `∑_σ (1 + hiMax(σ) + loMax(σ))`.
- On each residue class `(c0 mod Qc, t0 mod Qt)`, the divisibility conditions
  `M ∣ lc * Qc`, `M ∣ ht * Qt`, `Qc ∣ TB1 * Qt` make every floor affine in
  `(k, d)`, so the hull bound is convex in `k ∈ [0, k_max]` (proved in pure `ℤ`
  arithmetic without rationals or reals) and sublinear along the two boundary rays.
- A fast pure-Lean `Bool` checker `certifyTarget` verifies the finite residue-class
  boundary conditions inside the Lean kernel (`decide`), yielding
  `projLineCount X p0 ≤ 1 + N1 * t + N0` for ALL `t : ℕ` and ALL valid `c ≥ 0`.
-/

@[expose] public section

namespace StrongDirac

namespace HullCert

/-- A linear pencil class of projective points `(p, q, d)` with `|d| ≤ B1 * t + B0`
and `d ≡ rho (mod 2)`. -/
structure Pencil where
  p : ℤ
  q : ℤ
  rho : ℤ
  B1 : ℕ
  B0 : ℕ
  deriving DecidableEq, Repr

/-- Membership of a point `x : Pt` in a pencil `P` at parameter `t : ℕ`. -/
def Pencil.Mem (P : Pencil) (t : ℕ) (x : Pt) : Prop :=
  x.1 = P.p ∧ x.2.1 = P.q ∧
  -((P.B1 * t + P.B0 : ℕ) : ℤ) ≤ x.2.2 ∧
  x.2.2 ≤ ((P.B1 * t + P.B0 : ℕ) : ℤ) ∧
  x.2.2 % 2 = P.rho % 2

/-- Derived affine-interval parameters of a non-parallel pencil `P` relative to
base direction `(1, q0)` and scale `Lam`. -/
structure AffPencil where
  mu : ℕ
  lc : ℤ
  ht : ℤ
  h0 : ℤ
  zc : ℤ
  z0 : ℤ
  deriving DecidableEq, Repr

/-- Compute the derived affine-interval parameters of `P` relative to `(1, q0)` and `Lam`. -/
def Pencil.toAff (q0 : ℤ) (Lam : ℕ) (P : Pencil) : AffPencil :=
  let D : ℤ := P.q - q0 * P.p
  let f : ℕ := Lam / D.natAbs
  let sg : ℤ := if 0 < D then 1 else -1
  let lc : ℤ := -sg * (f : ℤ) * P.p
  { mu := 2 * f
    lc := lc
    ht := (f : ℤ) * (P.B1 : ℤ)
    h0 := (f : ℤ) * (P.B0 : ℤ)
    zc := lc
    z0 := sg * (f : ℤ) * P.rho }

/-- Whether `ap` can produce a coordinate `z ≡ σ (mod mu)` at offset `c`. -/
def AffPencil.isActive (ap : AffPencil) (c : ℤ) (σ : ℕ) : Bool :=
  ((σ : ℤ) - (ap.zc * c + ap.z0)) % (ap.mu : ℤ) == 0

/-- Maximum of `f` over a nonempty list (returns `0` on `[]`). -/
def listMax {α : Type*} (f : α → ℤ) : List α → ℤ
  | [] => 0
  | [a] => f a
  | a :: b :: rest => max (f a) (listMax f (b :: rest))

lemma le_listMax {α : Type*} (f : α → ℤ) {a : α} {l : List α} (ha : a ∈ l) :
    f a ≤ listMax f l := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.mem_singleton] at ha
      subst ha; exact le_rfl
    | cons y ys =>
      simp only [listMax]
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)

lemma listMax_le {α : Type*} (f : α → ℤ) {l : List α} (hne : l ≠ []) {B : ℤ}
    (h : ∀ a ∈ l, f a ≤ B) : listMax f l ≤ B := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => exact h x (List.mem_cons_self ..)
    | cons y ys =>
      simp only [listMax]
      exact max_le (h x (List.mem_cons_self ..))
        (ih (List.cons_ne_nil y ys) (fun a ha => h a (List.mem_cons_of_mem x ha)))

lemma mul_listMax_le {α : Type*} (f : α → ℤ) {l : List α} (hne : l ≠ [])
    {K B : ℤ} (h : ∀ a ∈ l, K * f a ≤ B) :
    K * listMax f l ≤ B := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => exact h x (List.mem_cons_self ..)
    | cons y ys =>
      simp only [listMax]
      rcases le_total (f x) (listMax f (y :: ys)) with hle | hle
      · rw [max_eq_right hle]
        exact ih (List.cons_ne_nil y ys) (fun a ha => h a (List.mem_cons_of_mem x ha))
      · rw [max_eq_left hle]
        exact h x (List.mem_cons_self ..)

lemma listMax_add_mul_le {α : Type*} {l : List α} (hne : l ≠ [])
    {d : ℤ} (hd : 0 ≤ d) (u v : α → ℤ) :
    listMax (fun a => u a + d * v a) l ≤ listMax u l + d * listMax v l := by
  refine listMax_le _ hne (fun a ha => ?_)
  have hu := le_listMax u ha
  have hv := le_listMax v ha
  have hdv : d * v a ≤ d * listMax v l := mul_le_mul_of_nonneg_left hv hd
  omega

lemma mul_listMax_convex {α : Type*} {l : List α} (hne : l ≠ [])
    {K k : ℤ} (hk0 : 0 ≤ k) (hkK : k ≤ K) (a m : α → ℤ) :
    K * listMax (fun x => a x + k * m x) l ≤
      (K - k) * listMax a l + k * listMax (fun x => a x + K * m x) l := by
  have hKk : 0 ≤ K - k := by omega
  refine mul_listMax_le _ hne (fun x hx => ?_)
  have h1 : (K - k) * a x ≤ (K - k) * listMax a l :=
    mul_le_mul_of_nonneg_left (le_listMax a hx) hKk
  have h2 : k * (a x + K * m x) ≤ k * listMax (fun y => a y + K * m y) l :=
    mul_le_mul_of_nonneg_left (le_listMax (fun y => a y + K * m y) hx) hk0
  have hid : K * (a x + k * m x) = (K - k) * a x + k * (a x + K * m x) := by ring
  omega

/-! ### Elementary `Int` Floor-Division (`/` = `Int.ediv`, `%` = `Int.emod`) Lemmas -/

lemma ediv_add_mul_of_emod_eq_zero {a d x M : ℤ} (hM : 0 < M) (hx : x % M = 0) :
    (a + d * x) / M = a / M + d * (x / M) := by
  have hx_eq : x = M * (x / M) := by
    have h := Int.mul_ediv_add_emod x M
    omega
  have hmul : a + d * x = a + M * (d * (x / M)) := by
    conv_lhs => rw [hx_eq]
    ring
  rw [hmul, Int.add_mul_ediv_left _ _ (ne_of_gt hM)]

lemma le_ediv_iff_mul_le {a k M : ℤ} (hM : 0 < M) :
    k ≤ a / M ↔ M * k ≤ a := by
  have h1 := Int.mul_ediv_add_emod a M
  have h2 := Int.emod_nonneg a (ne_of_gt hM)
  have h3 := Int.emod_lt_of_pos a hM
  constructor
  · intro hk
    have : M * k ≤ M * (a / M) := mul_le_mul_of_nonneg_left hk (le_of_lt hM)
    omega
  · intro hmk
    by_contra hlt
    push Not at hlt
    have hge : a / M + 1 ≤ k := by omega
    have : M * (a / M + 1) ≤ M * k := mul_le_mul_of_nonneg_left hge (le_of_lt hM)
    nlinarith

lemma ediv_add_ediv_add_one_nonneg {u v M : ℤ} (hM : 0 < M) (huv : 0 ≤ u + v) :
    0 ≤ u / M + v / M + 1 := by
  have hu1 := Int.mul_ediv_add_emod u M
  have hu2 := Int.emod_lt_of_pos u hM
  have hv1 := Int.mul_ediv_add_emod v M
  have hv2 := Int.emod_lt_of_pos v hM
  by_contra hlt
  push Not at hlt
  have hle : u / M + v / M + 2 ≤ 0 := by omega
  have hmul : M * (u / M + v / M + 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hM) hle
  nlinarith

/-! ### Active Residues, Hull Sum, Slope Sum, and Executable Checker -/

/-- Candidate residues `σ < M` hit by at least one pencil in `aps` at offset `c`.
Generating residues directly from each pencil's period `mu` avoids scanning all `M`
residues (for `N2`, this scans ≤ 10 active residues instead of 120). -/
def candSigmas (M : ℕ) (aps : List AffPencil) (c : ℤ) : List ℕ :=
  (aps.flatMap fun ap =>
    if ap.mu = 0 then []
    else
      let z : ℕ := ((ap.zc * c + ap.z0) % (ap.mu : ℤ)).toNat
      (List.range (M / ap.mu)).map fun k => z + k * ap.mu).eraseDups

/-- List of `(σ, activePencils)` for all `σ < M` where at least one pencil is active at `c`. -/
def activeList (M : ℕ) (aps : List AffPencil) (c : ℤ) : List (ℕ × List AffPencil) :=
  (candSigmas M aps c).filterMap fun σ =>
    let act := aps.filter (fun ap => ap.isActive c σ)
    if act.isEmpty then none else some (σ, act)

/-- Upper hull term `((lc * c + ht * t + h0) - σ) / M`. -/
def hiTerm (M : ℕ) (σ : ℕ) (c t : ℤ) (ap : AffPencil) : ℤ :=
  (ap.lc * c + ap.ht * t + ap.h0 - (σ : ℤ)) / (M : ℤ)

/-- Lower hull term `(σ - (lc * c - ht * t - h0)) / M`. -/
def loTerm (M : ℕ) (σ : ℕ) (c t : ℤ) (ap : AffPencil) : ℤ :=
  ((σ : ℤ) - (ap.lc * c - ap.ht * t - ap.h0)) / (M : ℤ)

/-- Hull upper bound summed over all active `(σ, act)` entries. -/
def hullSum (M : ℕ) (act : List (ℕ × List AffPencil)) (c t : ℤ) : ℤ :=
  act.foldl (fun acc entry =>
    let σ := entry.1
    let ps := entry.2
    acc + (listMax (hiTerm M σ c t) ps + listMax (loTerm M σ c t) ps + 1)) 0

/-- Ray slope sum over all active `(σ, act)` entries for step `(Δc, Δt)`. -/
def slopeSum (M : ℕ) (act : List (ℕ × List AffPencil)) (Δc Δt : ℤ) : ℤ :=
  act.foldl (fun acc entry =>
    let ps := entry.2
    acc + (listMax (fun ap => (ap.lc * Δc + ap.ht * Δt) / (M : ℤ)) ps +
           listMax (fun ap => (ap.ht * Δt - ap.lc * Δc) / (M : ℤ)) ps)) 0

/-- First step `tp : ℕ` where `A1 * tp + k0 ≥ 0` (for `A1 > 0`). -/
def firstStep (A1 : ℕ) (k0 : ℤ) : ℕ :=
  if 0 ≤ k0 then 0 else ((-k0).toNat + A1 - 1) / A1

/-- Check one `c0` residue across all `t0 ∈ [0, Qt)`. -/
def checkC0 (M : ℕ) (aps : List AffPencil) (TB1 TB0 Qc Qt N1 N0 A1 : ℕ) (c0 : ℤ) : Bool :=
  let act := activeList M aps c0
  let sl0 := slopeSum M act 0 (Qt : ℤ)
  let sl1 := slopeSum M act ((TB1 * Qt : ℕ) : ℤ) (Qt : ℤ)
  let needSlope : ℤ := ((N1 * Qt : ℕ) : ℤ)
  (sl0 ≤ needSlope) && (sl1 ≤ needSlope) &&
  ((List.range Qt).all fun t0 =>
    let k0 : ℤ := (((TB1 * t0 + TB0 : ℕ) : ℤ) - c0) / (Qc : ℤ)
    let tp : ℕ := firstStep A1 k0
    let tStart : ℤ := ((t0 + Qt * tp : ℕ) : ℤ)
    let cTop : ℤ := c0 + (Qc : ℤ) * ((A1 : ℤ) * (tp : ℤ) + k0)
    let needStart : ℤ := (N1 : ℤ) * tStart + (N0 : ℤ)
    (hullSum M act c0 tStart ≤ needStart) && (hullSum M act cTop tStart ≤ needStart))

/-- Check a subrange `j ∈ [lo, lo + len)` of `c0 = 2j + rho0` residues. -/
def checkC0Range (M : ℕ) (aps : List AffPencil) (TB1 TB0 Qc Qt N1 N0 A1 rho0 lo len : ℕ) : Bool :=
  (List.range len).all fun i =>
    checkC0 M aps TB1 TB0 Qc Qt N1 N0 A1 ((2 * (lo + i) + rho0 : ℕ) : ℤ)

/-- Header precondition checks of `certifyTarget` (excluding the `c0` loop). -/
def certifyHeader (q0 : ℤ) (Lam : ℕ) (pencils : List Pencil)
    (rho0 TB1 _TB0 Qc Qt : ℕ) : Bool :=
  let M := 2 * Lam
  let A1 := (TB1 * Qt) / Qc
  (0 < Lam) && (0 < Qc) && (0 < Qt) && (0 < A1) &&
  (Qc % 2 == 0) && ((TB1 * Qt) % Qc == 0) && (rho0 < 2) &&
  (pencils.all fun P =>
    let D := P.q - q0 * P.p
    let ap := P.toAff q0 Lam
    (D != 0) && ((Lam : ℤ) % D == 0) &&
    ((ap.lc * (Qc : ℤ)) % (M : ℤ) == 0) &&
    ((ap.ht * (Qt : ℤ)) % (M : ℤ) == 0))

/-- Top-level executable certificate verifying the hull upper bound for a target class
across all `t : ℕ` and all valid offsets `c ≥ 0`. -/
def certifyTarget (q0 : ℤ) (Lam : ℕ) (pencils : List Pencil)
    (rho0 TB1 TB0 Qc Qt N1 N0 : ℕ) : Bool :=
  let M := 2 * Lam
  let A1 := (TB1 * Qt) / Qc
  let aps := pencils.map (Pencil.toAff q0 Lam)
  certifyHeader q0 Lam pencils rho0 TB1 TB0 Qc Qt &&
  ((List.range (Qc / 2)).all fun j =>
    checkC0 M aps TB1 TB0 Qc Qt N1 N0 A1 ((2 * j + rho0 : ℕ) : ℤ))

lemma checkC0Range_append {M : ℕ} {aps : List AffPencil}
    {TB1 TB0 Qc Qt N1 N0 A1 rho0 lo len₁ len₂ : ℕ}
    (h1 : checkC0Range M aps TB1 TB0 Qc Qt N1 N0 A1 rho0 lo len₁ = true)
    (h2 : checkC0Range M aps TB1 TB0 Qc Qt N1 N0 A1 rho0 (lo + len₁) len₂ = true) :
    checkC0Range M aps TB1 TB0 Qc Qt N1 N0 A1 rho0 lo (len₁ + len₂) = true := by
  unfold checkC0Range at h1 h2 ⊢
  simp only [List.all_eq_true, List.mem_range] at h1 h2 ⊢
  intro i hi
  by_cases hlt : i < len₁
  · exact h1 i hlt
  · have h2i := h2 (i - len₁) (by omega)
    have heq : lo + len₁ + (i - len₁) = lo + i := by omega
    rwa [heq] at h2i

lemma certifyTarget_of_header_and_range
    {q0 : ℤ} {Lam : ℕ} {pencils : List Pencil}
    {rho0 TB1 TB0 Qc Qt N1 N0 : ℕ}
    (hhdr : certifyHeader q0 Lam pencils rho0 TB1 TB0 Qc Qt = true)
    (hrng : checkC0Range (2 * Lam) (pencils.map (Pencil.toAff q0 Lam))
      TB1 TB0 Qc Qt N1 N0 ((TB1 * Qt) / Qc) rho0 0 (Qc / 2) = true) :
    certifyTarget q0 Lam pencils rho0 TB1 TB0 Qc Qt N1 N0 = true := by
  unfold certifyTarget
  rw [hhdr, Bool.true_and]
  unfold checkC0Range at hrng
  simpa using hrng

/-! ### Algebraic Properties of `foldl` Sums -/

private lemma foldl_add_shift {α : Type*} (f : α → ℤ) (l : List α) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + l.foldl (fun acc x => acc + f x) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (init + f x), ih (f x)]
    ring

private lemma foldl_add_eq_sum {α : Type*} (f : α → ℤ) (l : List α) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add, List.map_cons, List.sum_cons]
    rw [foldl_add_shift, ih]

private lemma hullSum_eq_sum (M : ℕ) (act : List (ℕ × List AffPencil)) (c t : ℤ) :
    hullSum M act c t =
      (act.map fun entry =>
        listMax (hiTerm M entry.1 c t) entry.2 +
        listMax (loTerm M entry.1 c t) entry.2 + 1).sum :=
  foldl_add_eq_sum _ act

private lemma slopeSum_eq_sum (M : ℕ) (act : List (ℕ × List AffPencil)) (Δc Δt : ℤ) :
    slopeSum M act Δc Δt =
      (act.map fun entry =>
        listMax (fun ap => (ap.lc * Δc + ap.ht * Δt) / (M : ℤ)) entry.2 +
        listMax (fun ap => (ap.ht * Δt - ap.lc * Δc) / (M : ℤ)) entry.2).sum :=
  foldl_add_eq_sum _ act

private lemma list_sum_le_sum {α : Type*} {l : List α} (f g : α → ℤ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

private lemma list_sum_add {α : Type*} (l : List α) (f g : α → ℤ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma list_sum_mul_left {α : Type*} (l : List α) (K : ℤ) (f : α → ℤ) :
    K * (l.map f).sum = (l.map fun x => K * f x).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-! ### Ray Sublinearity and Pure-Integer Convexity of `hullSum` -/

lemma hullSum_ray_le {M : ℕ} (hM : 0 < M)
    {act : List (ℕ × List AffPencil)}
    (hne : ∀ entry ∈ act, entry.2 ≠ [])
    {c t Δc Δt : ℤ} {d : ℕ}
    (hdiv1 : ∀ entry ∈ act, ∀ ap ∈ entry.2, (ap.lc * Δc + ap.ht * Δt) % (M : ℤ) = 0)
    (hdiv2 : ∀ entry ∈ act, ∀ ap ∈ entry.2, (ap.ht * Δt - ap.lc * Δc) % (M : ℤ) = 0) :
    hullSum M act (c + (d : ℤ) * Δc) (t + (d : ℤ) * Δt) ≤
      hullSum M act c t + (d : ℤ) * slopeSum M act Δc Δt := by
  rw [hullSum_eq_sum, hullSum_eq_sum, slopeSum_eq_sum, list_sum_mul_left, ← list_sum_add]
  refine list_sum_le_sum _ _ (fun entry hentry => ?_)
  have hMpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hd0 : (0 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le d
  have hne_ps : entry.2 ≠ [] := hne entry hentry
  have hhi : listMax (hiTerm M entry.1 (c + (d : ℤ) * Δc) (t + (d : ℤ) * Δt)) entry.2 ≤
      listMax (hiTerm M entry.1 c t) entry.2 +
      (d : ℤ) * listMax (fun ap => (ap.lc * Δc + ap.ht * Δt) / (M : ℤ)) entry.2 := by
    refine listMax_le _ hne_ps (fun ap hap => ?_)
    have heq : hiTerm M entry.1 (c + (d : ℤ) * Δc) (t + (d : ℤ) * Δt) ap =
        hiTerm M entry.1 c t ap + (d : ℤ) * ((ap.lc * Δc + ap.ht * Δt) / (M : ℤ)) := by
      unfold hiTerm
      have hlin : ap.lc * (c + (d : ℤ) * Δc) + ap.ht * (t + (d : ℤ) * Δt) + ap.h0 - (entry.1 : ℤ) =
          (ap.lc * c + ap.ht * t + ap.h0 - (entry.1 : ℤ)) + (d : ℤ) * (ap.lc * Δc + ap.ht * Δt) := by
        ring
      rw [hlin, ediv_add_mul_of_emod_eq_zero hMpos (hdiv1 entry hentry ap hap)]
    rw [heq]
    have h1 := le_listMax (hiTerm M entry.1 c t) hap
    have h2 := mul_le_mul_of_nonneg_left
      (le_listMax (fun ap => (ap.lc * Δc + ap.ht * Δt) / (M : ℤ)) hap) hd0
    omega
  have hlo : listMax (loTerm M entry.1 (c + (d : ℤ) * Δc) (t + (d : ℤ) * Δt)) entry.2 ≤
      listMax (loTerm M entry.1 c t) entry.2 +
      (d : ℤ) * listMax (fun ap => (ap.ht * Δt - ap.lc * Δc) / (M : ℤ)) entry.2 := by
    refine listMax_le _ hne_ps (fun ap hap => ?_)
    have heq : loTerm M entry.1 (c + (d : ℤ) * Δc) (t + (d : ℤ) * Δt) ap =
        loTerm M entry.1 c t ap + (d : ℤ) * ((ap.ht * Δt - ap.lc * Δc) / (M : ℤ)) := by
      unfold loTerm
      have hlin : (entry.1 : ℤ) - (ap.lc * (c + (d : ℤ) * Δc) - ap.ht * (t + (d : ℤ) * Δt) - ap.h0) =
          ((entry.1 : ℤ) - (ap.lc * c - ap.ht * t - ap.h0)) + (d : ℤ) * (ap.ht * Δt - ap.lc * Δc) := by
        ring
      rw [hlin, ediv_add_mul_of_emod_eq_zero hMpos (hdiv2 entry hentry ap hap)]
    rw [heq]
    have h1 := le_listMax (loTerm M entry.1 c t) hap
    have h2 := mul_le_mul_of_nonneg_left
      (le_listMax (fun ap => (ap.ht * Δt - ap.lc * Δc) / (M : ℤ)) hap) hd0
    omega
  linarith

lemma hullSum_convex_le {M : ℕ} (hM : 0 < M)
    {act : List (ℕ × List AffPencil)}
    (hne : ∀ entry ∈ act, entry.2 ≠ [])
    {c0 t Qc k K B : ℤ} (hk0 : 0 ≤ k) (hkK : k ≤ K)
    (hdiv : ∀ entry ∈ act, ∀ ap ∈ entry.2, (ap.lc * Qc) % (M : ℤ) = 0)
    (hlo : hullSum M act c0 t ≤ B)
    (hhi : hullSum M act (c0 + Qc * K) t ≤ B) :
    hullSum M act (c0 + Qc * k) t ≤ B := by
  by_cases hK0 : K = 0
  · have hk : k = 0 := by omega
    subst hk
    simpa using hlo
  · have hKpos : 0 < K := by omega
    have hMpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
    have hmul : K * hullSum M act (c0 + Qc * k) t ≤
        (K - k) * hullSum M act c0 t + k * hullSum M act (c0 + Qc * K) t := by
      rw [hullSum_eq_sum, hullSum_eq_sum, hullSum_eq_sum,
          list_sum_mul_left, list_sum_mul_left, list_sum_mul_left, ← list_sum_add]
      refine list_sum_le_sum _ _ (fun entry hentry => ?_)
      have hne_ps : entry.2 ≠ [] := hne entry hentry
      have hhi_eq : ∀ s : ℤ,
          listMax (hiTerm M entry.1 (c0 + Qc * s) t) entry.2 =
          listMax (fun ap => hiTerm M entry.1 c0 t ap + s * ((ap.lc * Qc) / (M : ℤ))) entry.2 := by
        intro s
        have hfun : ∀ ap ∈ entry.2,
            hiTerm M entry.1 (c0 + Qc * s) t ap =
            hiTerm M entry.1 c0 t ap + s * ((ap.lc * Qc) / (M : ℤ)) := by
          intro ap hap
          unfold hiTerm
          have hlin : ap.lc * (c0 + Qc * s) + ap.ht * t + ap.h0 - (entry.1 : ℤ) =
              (ap.lc * c0 + ap.ht * t + ap.h0 - (entry.1 : ℤ)) + s * (ap.lc * Qc) := by ring
          rw [hlin, ediv_add_mul_of_emod_eq_zero hMpos (hdiv entry hentry ap hap)]
        apply le_antisymm
        · refine listMax_le _ hne_ps (fun ap hap => ?_)
          rw [hfun ap hap]; exact le_listMax _ hap
        · refine listMax_le _ hne_ps (fun ap hap => ?_)
          rw [← hfun ap hap]; exact le_listMax _ hap
      have hlo_eq : ∀ s : ℤ,
          listMax (loTerm M entry.1 (c0 + Qc * s) t) entry.2 =
          listMax (fun ap => loTerm M entry.1 c0 t ap + s * ((-(ap.lc * Qc)) / (M : ℤ))) entry.2 := by
        intro s
        have hdiv_neg : ∀ ap ∈ entry.2, (-(ap.lc * Qc)) % (M : ℤ) = 0 := by
          intro ap hap
          have hd := hdiv entry hentry ap hap
          have h1 := Int.mul_ediv_add_emod (ap.lc * Qc) (M : ℤ)
          have h2 : -(ap.lc * Qc) = (M : ℤ) * (-((ap.lc * Qc) / (M : ℤ))) := by
            linear_combination h1 - hd
          rw [h2, Int.mul_emod_right]
        have hfun : ∀ ap ∈ entry.2,
            loTerm M entry.1 (c0 + Qc * s) t ap =
            loTerm M entry.1 c0 t ap + s * ((-(ap.lc * Qc)) / (M : ℤ)) := by
          intro ap hap
          unfold loTerm
          have hlin : (entry.1 : ℤ) - (ap.lc * (c0 + Qc * s) - ap.ht * t - ap.h0) =
              ((entry.1 : ℤ) - (ap.lc * c0 - ap.ht * t - ap.h0)) + s * (-(ap.lc * Qc)) := by ring
          rw [hlin, ediv_add_mul_of_emod_eq_zero hMpos (hdiv_neg ap hap)]
        apply le_antisymm
        · refine listMax_le _ hne_ps (fun ap hap => ?_)
          rw [hfun ap hap]; exact le_listMax _ hap
        · refine listMax_le _ hne_ps (fun ap hap => ?_)
          rw [← hfun ap hap]; exact le_listMax _ hap
      have c1 := mul_listMax_convex hne_ps hk0 hkK
        (hiTerm M entry.1 c0 t) (fun ap => (ap.lc * Qc) / (M : ℤ))
      have c2 := mul_listMax_convex hne_ps hk0 hkK
        (loTerm M entry.1 c0 t) (fun ap => (-(ap.lc * Qc)) / (M : ℤ))
      rw [← hhi_eq k, ← hhi_eq K] at c1
      rw [← hlo_eq k, ← hlo_eq K] at c2
      linarith
    have hB : (K - k) * hullSum M act c0 t + k * hullSum M act (c0 + Qc * K) t ≤ K * B := by
      have h1 : (K - k) * hullSum M act c0 t ≤ (K - k) * B :=
        mul_le_mul_of_nonneg_left hlo (by omega)
      have h2 : k * hullSum M act (c0 + Qc * K) t ≤ k * B :=
        mul_le_mul_of_nonneg_left hhi hk0
      linarith
    have hKB : K * hullSum M act (c0 + Qc * k) t ≤ K * B := le_trans hmul hB
    exact le_of_mul_le_mul_left hKB hKpos

/-! ### Step-1 Soundness: `certifyTarget = true` Implies `hullSum ≤ N1 * t + N0` -/

lemma firstStep_le_iff {A1 : ℕ} (hA1 : 0 < A1) {k0 : ℤ} {t' : ℕ} :
    firstStep A1 k0 ≤ t' ↔ 0 ≤ (A1 : ℤ) * (t' : ℤ) + k0 := by
  unfold firstStep
  split_ifs with hk
  · constructor
    · intro _; have : (0 : ℤ) ≤ (A1 : ℤ) * (t' : ℤ) := by positivity
      omega
    · intro _; exact Nat.zero_le _
  · have hneg : 0 < -k0 := by omega
    have hnat : ((-k0).toNat : ℤ) = -k0 := Int.toNat_of_nonneg (by omega)
    constructor
    · intro hle
      have h1 : (-k0).toNat ≤ A1 * t' := by
        have hdiv := Nat.div_add_mod ((-k0).toNat + A1 - 1) A1
        have hmod := Nat.mod_lt ((-k0).toNat + A1 - 1) hA1
        have hmul : A1 * (((-k0).toNat + A1 - 1) / A1) ≤ A1 * t' := Nat.mul_le_mul_left A1 hle
        omega
      have h1Z : ((-k0).toNat : ℤ) ≤ ((A1 * t' : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at h1Z
      omega
    · intro hge
      have h1 : (-k0).toNat ≤ A1 * t' := by
        have h1Z : ((-k0).toNat : ℤ) ≤ ((A1 * t' : ℕ) : ℤ) := by push_cast; omega
        exact_mod_cast h1Z
      have hdiv := Nat.div_add_mod ((-k0).toNat + A1 - 1) A1
      have hmod := Nat.mod_lt ((-k0).toNat + A1 - 1) hA1
      have hlt : ((-k0).toNat + A1 - 1) / A1 < t' + 1 := by
        by_contra hge2
        push Not at hge2
        have hmul : A1 * (t' + 1) ≤ A1 * (((-k0).toNat + A1 - 1) / A1) :=
          Nat.mul_le_mul_left A1 hge2
        have hmul_exp : A1 * (t' + 1) = A1 * t' + A1 := by ring
        omega
      omega

private lemma mem_candSigmas_of_active {M : ℕ} {aps : List AffPencil} {c : ℤ}
    {ap : AffPencil} (hap : ap ∈ aps) (hmu : 0 < ap.mu) (hdvd : ap.mu ∣ M)
    {σ : ℕ} (hσ : σ < M) (hact : ap.isActive c σ = true) :
    σ ∈ candSigmas M aps c := by
  unfold candSigmas
  rw [List.mem_eraseDups, List.mem_flatMap]
  refine ⟨ap, hap, ?_⟩
  simp only [ne_of_gt hmu, ↓reduceIte, List.mem_map]
  have hmuZ : (0 : ℤ) < (ap.mu : ℤ) := by exact_mod_cast hmu
  unfold AffPencil.isActive at hact
  rw [beq_iff_eq] at hact
  set z : ℕ := ((ap.zc * c + ap.z0) % (ap.mu : ℤ)).toNat
  have hz_eq : (z : ℤ) = (ap.zc * c + ap.z0) % (ap.mu : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hmuZ))
  have hσmod : ((σ : ℤ) % (ap.mu : ℤ)) = (z : ℤ) := by
    rw [hz_eq]
    have h1 := Int.sub_emod (σ : ℤ) (ap.zc * c + ap.z0) (ap.mu : ℤ)
    rw [hact] at h1
    have hlt1 := Int.emod_lt_of_pos (σ : ℤ) hmuZ
    have hnn1 := Int.emod_nonneg (σ : ℤ) (ne_of_gt hmuZ)
    have hlt2 := Int.emod_lt_of_pos (ap.zc * c + ap.z0) hmuZ
    have hnn2 := Int.emod_nonneg (ap.zc * c + ap.z0) (ne_of_gt hmuZ)
    have hd : (ap.mu : ℤ) ∣ ((σ : ℤ) % (ap.mu : ℤ) - (ap.zc * c + ap.z0) % (ap.mu : ℤ)) :=
      Int.dvd_of_emod_eq_zero h1.symm
    rcases hd with ⟨q, hq⟩
    have hq0 : q = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : (ap.mu : ℤ) * q ≤ -(ap.mu : ℤ) := by nlinarith
        omega
      · have : (ap.mu : ℤ) ≤ (ap.mu : ℤ) * q := by nlinarith
        omega
    subst hq0
    rw [mul_zero] at hq
    omega
  have hσmod_nat : σ % ap.mu = z := by
    have : ((σ % ap.mu : ℕ) : ℤ) = (z : ℤ) := by rw [Int.natCast_emod]; exact hσmod
    exact_mod_cast this
  refine ⟨σ / ap.mu, List.mem_range.mpr ?_, ?_⟩
  · have hM_eq : ap.mu * (M / ap.mu) = M := Nat.mul_div_cancel' hdvd
    have hdiv := Nat.div_add_mod σ ap.mu
    by_contra hge
    push Not at hge
    have : ap.mu * (M / ap.mu) ≤ ap.mu * (σ / ap.mu) := Nat.mul_le_mul_left ap.mu hge
    omega
  · have hdiv := Nat.div_add_mod σ ap.mu
    rw [hσmod_nat] at hdiv
    linarith

private lemma activeList_invariant_mod {M : ℕ} {aps : List AffPencil} {c0 c : ℤ}
    (hmod : ∀ ap ∈ aps, (ap.zc * (c - c0)) % (ap.mu : ℤ) = 0) :
    activeList M aps c = activeList M aps c0 := by
  have hcand : candSigmas M aps c = candSigmas M aps c0 := by
    unfold candSigmas
    congr 1
    refine List.flatMap_congr (fun ap hap => ?_)
    have hsum : ap.zc * c + ap.z0 = (ap.zc * c0 + ap.z0) + ap.zc * (c - c0) := by ring
    have hEq : (ap.zc * c + ap.z0) % (ap.mu : ℤ) = (ap.zc * c0 + ap.z0) % (ap.mu : ℤ) := by
      rw [hsum, Int.add_emod, hmod ap hap, add_zero, Int.emod_emod]
    rw [hEq]
  unfold activeList
  rw [hcand]
  congr 1
  funext σ
  have hfilt : aps.filter (fun ap => ap.isActive c σ) = aps.filter (fun ap => ap.isActive c0 σ) := by
    refine List.filter_congr (fun ap hap => ?_)
    unfold AffPencil.isActive
    have hdiff : ((σ : ℤ) - (ap.zc * c + ap.z0)) =
        ((σ : ℤ) - (ap.zc * c0 + ap.z0)) - ap.zc * (c - c0) := by ring
    have hd := hmod ap hap
    have hEq : ((σ : ℤ) - (ap.zc * c + ap.z0)) % (ap.mu : ℤ) =
        ((σ : ℤ) - (ap.zc * c0 + ap.z0)) % (ap.mu : ℤ) := by
      rw [hdiff, Int.sub_emod, hd, sub_zero, Int.emod_emod]
    rw [hEq]
  rw [hfilt]

private lemma activeList_ne {M : ℕ} {aps : List AffPencil} {c : ℤ}
    {entry : ℕ × List AffPencil} (hentry : entry ∈ activeList M aps c) :
    entry.2 ≠ [] := by
  simp only [activeList, List.mem_filterMap] at hentry
  rcases hentry with ⟨σ, _, hsome⟩
  by_cases hemp : (aps.filter (fun ap => ap.isActive c σ)).isEmpty = true
  · simp [hemp] at hsome
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome
    rw [← hsome]
    intro hnil
    dsimp only at hnil
    rw [hnil] at hemp
    simp at hemp

private lemma activeList_mem_aps {M : ℕ} {aps : List AffPencil} {c : ℤ}
    {entry : ℕ × List AffPencil} (hentry : entry ∈ activeList M aps c)
    {ap : AffPencil} (hap : ap ∈ entry.2) :
    ap ∈ aps := by
  simp only [activeList, List.mem_filterMap] at hentry
  rcases hentry with ⟨σ, _, hsome⟩
  by_cases hemp : (aps.filter (fun ap => ap.isActive c σ)).isEmpty = true
  · simp [hemp] at hsome
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsome
    rw [← hsome] at hap
    exact (List.mem_filter.mp hap).1

/-- Step 1: from `certifyTarget = true`, deduce `hullSum ≤ N1 * t + N0` at `(c, t)`. -/
theorem hullSum_le_of_certifyTarget
    {q0 : ℤ} {Lam : ℕ} {pencils : List Pencil}
    {rho0 TB1 TB0 Qc Qt N1 N0 : ℕ}
    (hcert : certifyTarget q0 Lam pencils rho0 TB1 TB0 Qc Qt N1 N0 = true)
    {t : ℕ} {c : ℤ}
    (hc0 : 0 ≤ c) (hc_hi : c ≤ ((TB1 * t + TB0 : ℕ) : ℤ))
    (hc_par : c % 2 = (rho0 : ℤ)) :
    hullSum (2 * Lam) (activeList (2 * Lam) (pencils.map (Pencil.toAff q0 Lam)) c) c (t : ℤ) ≤
      (N1 : ℤ) * (t : ℤ) + (N0 : ℤ) := by
  unfold certifyTarget certifyHeader at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, List.all_eq_true] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨⟨⟨hLam, hQc⟩, hQt⟩, hA1⟩, hQc2⟩, hTB1div⟩, hrho0⟩, hPall⟩, hCall⟩
  set M := 2 * Lam
  set A1 := (TB1 * Qt) / Qc
  set aps := pencils.map (Pencil.toAff q0 Lam)
  have hM : 0 < M := by omega
  have hQcpos : (0 : ℤ) < (Qc : ℤ) := by exact_mod_cast hQc
  have hA1_mul : A1 * Qc = TB1 * Qt := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hTB1div)
  -- Decompose c = c0 + Qc * k
  set c0 : ℤ := c % (Qc : ℤ)
  set k : ℤ := c / (Qc : ℤ)
  have hc0_nn : 0 ≤ c0 := Int.emod_nonneg c (ne_of_gt hQcpos)
  have hc0_lt : c0 < (Qc : ℤ) := Int.emod_lt_of_pos c hQcpos
  have hc_decomp : c = c0 + (Qc : ℤ) * k := by
    have h := Int.mul_ediv_add_emod c (Qc : ℤ)
    linarith
  have hk_nn : 0 ≤ k := Int.ediv_nonneg hc0 (le_of_lt hQcpos)
  have hc0_par : c0 % 2 = (rho0 : ℤ) := by
    have h2dvd : (2 : ℤ) ∣ (Qc : ℤ) := by omega
    rcases h2dvd with ⟨q2, hq2⟩
    have h1 : c0 = c - 2 * (q2 * k) := by
      have : (Qc : ℤ) * k = 2 * (q2 * k) := by rw [hq2]; ring
      linarith
    rw [h1, Int.sub_emod, Int.mul_emod_right, sub_zero, Int.emod_emod, hc_par]
  -- Write c0 = 2 * j + rho0 with j < Qc / 2
  set j : ℕ := ((c0 - (rho0 : ℤ)) / 2).toNat
  have hc0_eq_j : ((2 * j + rho0 : ℕ) : ℤ) = c0 := by
    have hsub : 0 ≤ c0 - (rho0 : ℤ) := by omega
    have hdiv2 := Int.mul_ediv_add_emod (c0 - (rho0 : ℤ)) 2
    have hmod2 : (c0 - (rho0 : ℤ)) % 2 = 0 := by
      rw [Int.sub_emod, hc0_par]; omega
    have hjZ : (j : ℤ) = (c0 - (rho0 : ℤ)) / 2 :=
      Int.toNat_of_nonneg (Int.ediv_nonneg hsub (by omega))
    push_cast; omega
  have hj_lt : j < Qc / 2 := by
    have : (2 * j + rho0 : ℕ) < Qc := by
      have : ((2 * j + rho0 : ℕ) : ℤ) < (Qc : ℤ) := by rw [hc0_eq_j]; exact hc0_lt
      exact_mod_cast this
    omega
  -- Unpack checkC0 at c0
  have hC0 := hCall j (List.mem_range.mpr hj_lt)
  rw [hc0_eq_j] at hC0
  unfold checkC0 at hC0
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hC0
  rcases hC0 with ⟨⟨hsl0, hsl1⟩, hT_all⟩
  set act := activeList M aps c0
  -- Show activeList M aps c = act
  have hact_eq_c : activeList M aps c = act := by
    refine activeList_invariant_mod (fun ap hap => ?_)
    rcases List.mem_map.mp hap with ⟨P, hP, rfl⟩
    have hPinfo := hPall P hP
    have hDdvd : (Lam : ℤ) % (P.q - q0 * P.p) = 0 := hPinfo.1.1.2
    have hQc_div : ((P.toAff q0 Lam).lc * (Qc : ℤ)) % (M : ℤ) = 0 := hPinfo.1.2
    have hmu_dvd_M : ((P.toAff q0 Lam).mu : ℤ) ∣ (M : ℤ) := by
      have hnat_dvd : (P.q - q0 * P.p).natAbs ∣ Lam :=
        Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero hDdvd)
      have h2dvd : 2 * (Lam / (P.q - q0 * P.p).natAbs) ∣ 2 * Lam :=
        Nat.mul_dvd_mul_left 2 (Nat.div_dvd_of_dvd hnat_dvd)
      exact_mod_cast h2dvd
    have hM_dvd : (M : ℤ) ∣ (P.toAff q0 Lam).zc * (c - c0) := by
      have hcc0 : c - c0 = (Qc : ℤ) * k := by linarith
      have hzc : (P.toAff q0 Lam).zc = (P.toAff q0 Lam).lc := rfl
      rw [hcc0, hzc]
      have hrew : (P.toAff q0 Lam).lc * ((Qc : ℤ) * k) = ((P.toAff q0 Lam).lc * (Qc : ℤ)) * k := by
        ring
      rw [hrew]
      exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hQc_div) k
    exact Int.emod_eq_zero_of_dvd (dvd_trans hmu_dvd_M hM_dvd)
  rw [hact_eq_c]
  -- Unpack t = t0 + Qt * t'
  set t0 : ℕ := t % Qt
  set t' : ℕ := t / Qt
  have ht0_lt : t0 < Qt := Nat.mod_lt t hQt
  have ht_eq : t = t0 + Qt * t' := by
    dsimp only [t0, t']
    have := Nat.div_add_mod t Qt
    omega
  have hT0 := hT_all t0 (List.mem_range.mpr ht0_lt)
  set k0 : ℤ := (((TB1 * t0 + TB0 : ℕ) : ℤ) - c0) / (Qc : ℤ)
  set tp : ℕ := firstStep A1 k0
  set tStart : ℤ := ((t0 + Qt * tp : ℕ) : ℤ)
  set cTop : ℤ := c0 + (Qc : ℤ) * ((A1 : ℤ) * (tp : ℤ) + k0)
  set needStart : ℤ := (N1 : ℤ) * tStart + (N0 : ℤ)
  have hray0_base : hullSum M act c0 tStart ≤ needStart := hT0.1
  have hray1_base : hullSum M act cTop tStart ≤ needStart := hT0.2
  -- Show 0 ≤ k ≤ kmax = A1 * t' + k0
  set kmax : ℤ := (A1 : ℤ) * (t' : ℤ) + k0
  have hA1_mulZ : (A1 : ℤ) * (Qc : ℤ) = (TB1 : ℤ) * (Qt : ℤ) := by
    have h : ((A1 * Qc : ℕ) : ℤ) = ((TB1 * Qt : ℕ) : ℤ) := by exact_mod_cast hA1_mul
    push_cast at h; exact h
  have hkmax_eq : kmax = (((TB1 * t + TB0 : ℕ) : ℤ) - c0) / (Qc : ℤ) := by
    have hlin : ((TB1 * t + TB0 : ℕ) : ℤ) - c0 =
        (((TB1 * t0 + TB0 : ℕ) : ℤ) - c0) + (Qc : ℤ) * ((A1 : ℤ) * (t' : ℤ)) := by
      rw [ht_eq]; push_cast
      linear_combination -(t' : ℤ) * hA1_mulZ
    rw [hlin, Int.add_mul_ediv_left _ _ (ne_of_gt hQcpos)]
    ring
  have hk_le_kmax : k ≤ kmax := by
    rw [hkmax_eq, le_ediv_iff_mul_le hQcpos]
    linarith
  have hkmax_nn : 0 ≤ kmax := le_trans hk_nn hk_le_kmax
  have htp_le : tp ≤ t' := (firstStep_le_iff hA1).mpr hkmax_nn
  set d : ℕ := t' - tp
  have ht'_eq : (t' : ℤ) = (tp : ℤ) + (d : ℤ) := by omega
  have ht_step : (t : ℤ) = tStart + (d : ℤ) * (Qt : ℤ) := by
    have htZ : (t : ℤ) = (t0 : ℤ) + (Qt : ℤ) * (t' : ℤ) := by exact_mod_cast ht_eq
    have htsZ : tStart = (t0 : ℤ) + (Qt : ℤ) * (tp : ℤ) := by dsimp only [tStart]; push_cast; rfl
    rw [htZ, htsZ, ht'_eq]; ring
  have hctop_step : c0 + (Qc : ℤ) * kmax = cTop + (d : ℤ) * ((TB1 * Qt : ℕ) : ℤ) := by
    dsimp only [cTop, kmax]
    rw [ht'_eq]; push_cast
    linear_combination (d : ℤ) * hA1_mulZ
  -- Divisibility helpers for activeList entries
  have hact_ne : ∀ entry ∈ act, entry.2 ≠ [] := fun _ h => activeList_ne h
  have hact_mem_aps : ∀ entry ∈ act, ∀ ap ∈ entry.2, ap ∈ aps := fun _ h _ hap =>
    activeList_mem_aps h hap
  have haps_div_Qc : ∀ ap ∈ aps, (ap.lc * (Qc : ℤ)) % (M : ℤ) = 0 := by
    intro ap hap; rcases List.mem_map.mp hap with ⟨P, hP, rfl⟩; exact (hPall P hP).1.2
  have haps_div_Qt : ∀ ap ∈ aps, (ap.ht * (Qt : ℤ)) % (M : ℤ) = 0 := by
    intro ap hap; rcases List.mem_map.mp hap with ⟨P, hP, rfl⟩; exact (hPall P hP).2
  have haps_div_TB1Qt : ∀ ap ∈ aps, (ap.lc * ((TB1 * Qt : ℕ) : ℤ)) % (M : ℤ) = 0 := by
    intro ap hap
    have h1 := haps_div_Qc ap hap
    have hrew : ap.lc * ((TB1 * Qt : ℕ) : ℤ) = (ap.lc * (Qc : ℤ)) * (A1 : ℤ) := by
      push_cast; linear_combination -ap.lc * hA1_mulZ
    rw [hrew, Int.mul_emod, h1, zero_mul, Int.zero_emod]
  have hdiv_sum : ∀ {Δc : ℤ}, (∀ ap ∈ aps, (ap.lc * Δc) % (M : ℤ) = 0) →
      (∀ entry ∈ act, ∀ ap ∈ entry.2, (ap.lc * Δc + ap.ht * (Qt : ℤ)) % (M : ℤ) = 0) ∧
      (∀ entry ∈ act, ∀ ap ∈ entry.2, (ap.ht * (Qt : ℤ) - ap.lc * Δc) % (M : ℤ) = 0) := by
    intro Δc hΔc
    constructor
    · intro entry hentry ap hap
      have hap' := hact_mem_aps entry hentry ap hap
      rw [Int.add_emod, hΔc ap hap', haps_div_Qt ap hap', add_zero, Int.zero_emod]
    · intro entry hentry ap hap
      have hap' := hact_mem_aps entry hentry ap hap
      rw [Int.sub_emod, haps_div_Qt ap hap', hΔc ap hap', sub_zero, Int.zero_emod]
  -- Bound ray 0 and ray 1 at t
  have hneed_eq : (N1 : ℤ) * (t : ℤ) + (N0 : ℤ) = needStart + (d : ℤ) * ((N1 * Qt : ℕ) : ℤ) := by
    dsimp only [needStart]; rw [ht_step]; push_cast; ring
  have hray0_t : hullSum M act c0 (t : ℤ) ≤ (N1 : ℤ) * (t : ℤ) + (N0 : ℤ) := by
    have hdiv0 := hdiv_sum (Δc := 0) (fun ap _ => by simp)
    have hle := hullSum_ray_le hM hact_ne (c := c0) (t := tStart) (Δc := 0) (Δt := (Qt : ℤ))
      (d := d) hdiv0.1 hdiv0.2
    simp only [mul_zero, add_zero] at hle
    rw [← ht_step] at hle
    have hmul : (d : ℤ) * slopeSum M act 0 (Qt : ℤ) ≤ (d : ℤ) * ((N1 * Qt : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left hsl0 (by exact_mod_cast Nat.zero_le d)
    linarith
  have hray1_t : hullSum M act (c0 + (Qc : ℤ) * kmax) (t : ℤ) ≤ (N1 : ℤ) * (t : ℤ) + (N0 : ℤ) := by
    have hdiv1 := hdiv_sum (Δc := ((TB1 * Qt : ℕ) : ℤ)) haps_div_TB1Qt
    have hle := hullSum_ray_le hM hact_ne (c := cTop) (t := tStart)
      (Δc := ((TB1 * Qt : ℕ) : ℤ)) (Δt := (Qt : ℤ)) (d := d) hdiv1.1 hdiv1.2
    rw [← ht_step, ← hctop_step] at hle
    have hmul : (d : ℤ) * slopeSum M act ((TB1 * Qt : ℕ) : ℤ) (Qt : ℤ) ≤
        (d : ℤ) * ((N1 * Qt : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left hsl1 (by exact_mod_cast Nat.zero_le d)
    linarith
  -- Apply pure-integer convexity at fixed t
  rw [hc_decomp]
  exact hullSum_convex_le hM hact_ne hk_nn hk_le_kmax
    (fun entry hentry ap hap => haps_div_Qc ap (hact_mem_aps entry hentry ap hap))
    hray0_t hray1_t

/-! ### Step-2 Soundness: Connecting `hullSum` to `projLineCount` -/

/-- Scaled projective slope label relative to `(1, q0, c)` with scale `Lam`. -/
def zLabel (q0 c : ℤ) (Lam : ℕ) (x : Pt) : Option ℤ :=
  let D := x.2.1 - q0 * x.1
  if D = 0 then none else some (((Lam : ℤ) * (x.2.2 - c * x.1)) / D)

private lemma card_biUnion_active_le {M : ℕ} (hM : 0 < M)
    (act : List (ℕ × List AffPencil)) (c t : ℤ)
    (hne : ∀ entry ∈ act, entry.2 ≠ [])
    (hnonneg : ∀ entry ∈ act, ∀ ap ∈ entry.2, 0 ≤ ap.ht * t + ap.h0) :
    (((act.toFinset).biUnion fun entry =>
      (Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                  (listMax (hiTerm M entry.1 c t) entry.2)).image
        (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card : ℤ) ≤
    hullSum M act c t := by
  have hMpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hnn_entry : ∀ entry ∈ act,
      0 ≤ listMax (hiTerm M entry.1 c t) entry.2 +
          listMax (loTerm M entry.1 c t) entry.2 + 1 := by
    intro entry hentry
    rcases List.exists_mem_of_ne_nil _ (hne entry hentry) with ⟨ap, hap⟩
    have h1 : hiTerm M entry.1 c t ap ≤ listMax (hiTerm M entry.1 c t) entry.2 :=
      le_listMax (hiTerm M entry.1 c t) hap
    have h2 : loTerm M entry.1 c t ap ≤ listMax (loTerm M entry.1 c t) entry.2 :=
      le_listMax (loTerm M entry.1 c t) hap
    have h3 := hnonneg entry hentry ap hap
    have huv : 0 ≤ (ap.lc * c + ap.ht * t + ap.h0 - (entry.1 : ℤ)) +
        ((entry.1 : ℤ) - (ap.lc * c - ap.ht * t - ap.h0)) := by linarith
    have h4 := ediv_add_ediv_add_one_nonneg hMpos huv
    dsimp only [hiTerm, loTerm] at h1 h2
    omega
  have hstep : ∀ entry ∈ act,
      (((Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                    (listMax (hiTerm M entry.1 c t) entry.2)).image
          (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card : ℤ) ≤
      listMax (hiTerm M entry.1 c t) entry.2 + listMax (loTerm M entry.1 c t) entry.2 + 1 := by
    intro entry hentry
    have himg : ((Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                    (listMax (hiTerm M entry.1 c t) entry.2)).image
          (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card ≤
        (Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                    (listMax (hiTerm M entry.1 c t) entry.2)).card := Finset.card_image_le
    rw [Int.card_Icc] at himg
    have himgZ : (((Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                    (listMax (hiTerm M entry.1 c t) entry.2)).image
          (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card : ℤ) ≤
        ((listMax (hiTerm M entry.1 c t) entry.2 + 1 -
          (-listMax (loTerm M entry.1 c t) entry.2)).toNat : ℤ) := by exact_mod_cast himg
    have hnn := hnn_entry entry hentry
    have htoNat : ((listMax (hiTerm M entry.1 c t) entry.2 + 1 -
          (-listMax (loTerm M entry.1 c t) entry.2)).toNat : ℤ) =
        listMax (hiTerm M entry.1 c t) entry.2 + listMax (loTerm M entry.1 c t) entry.2 + 1 := by
      have : listMax (hiTerm M entry.1 c t) entry.2 + 1 -
          (-listMax (loTerm M entry.1 c t) entry.2) =
          listMax (hiTerm M entry.1 c t) entry.2 + listMax (loTerm M entry.1 c t) entry.2 + 1 := by
        ring
      rw [this, Int.toNat_of_nonneg hnn]
    omega
  have h1 : ((act.toFinset).biUnion fun entry =>
      (Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                  (listMax (hiTerm M entry.1 c t) entry.2)).image
        (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card ≤
      ∑ entry ∈ act.toFinset,
        ((Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                     (listMax (hiTerm M entry.1 c t) entry.2)).image
          (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card :=
    Finset.card_biUnion_le
  have h1Z : (((act.toFinset).biUnion fun entry =>
      (Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                  (listMax (hiTerm M entry.1 c t) entry.2)).image
        (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card : ℤ) ≤
      ∑ entry ∈ act.toFinset,
        (((Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                      (listMax (hiTerm M entry.1 c t) entry.2)).image
          (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card : ℤ) := by
    exact_mod_cast h1
  have h2Z : ∑ entry ∈ act.toFinset,
        (((Finset.Icc (-listMax (loTerm M entry.1 c t) entry.2)
                      (listMax (hiTerm M entry.1 c t) entry.2)).image
          (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))).card : ℤ) ≤
      ∑ entry ∈ act.toFinset,
        (listMax (hiTerm M entry.1 c t) entry.2 + listMax (loTerm M entry.1 c t) entry.2 + 1) :=
    Finset.sum_le_sum (fun entry hentry => hstep entry (List.mem_toFinset.mp hentry))
  have h3Z : ∑ entry ∈ act.toFinset,
        (listMax (hiTerm M entry.1 c t) entry.2 + listMax (loTerm M entry.1 c t) entry.2 + 1) ≤
      hullSum M act c t := by
    rw [hullSum_eq_sum]
    clear h1 h1Z h2Z hstep
    induction act with
    | nil => simp
    | cons x xs ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      have hne' : ∀ e ∈ xs, e.2 ≠ [] := fun e he => hne e (List.mem_cons_of_mem x he)
      have hnonneg' : ∀ e ∈ xs, ∀ ap ∈ e.2, 0 ≤ ap.ht * t + ap.h0 :=
        fun e he => hnonneg e (List.mem_cons_of_mem x he)
      have hnn' : ∀ e ∈ xs, 0 ≤ listMax (hiTerm M e.1 c t) e.2 +
          listMax (loTerm M e.1 c t) e.2 + 1 := fun e he => hnn_entry e (List.mem_cons_of_mem x he)
      have hih := ih hne' hnonneg' hnn'
      by_cases hmem : x ∈ xs.toFinset
      · rw [Finset.insert_eq_of_mem hmem]
        have hx0 := hnn_entry x (List.mem_cons_self ..)
        omega
      · rw [Finset.sum_insert hmem]
        omega
  exact le_trans h1Z (le_trans h2Z h3Z)

/-- **Master Soundness Theorem for `certifyTarget`**:
If `certifyTarget q0 Lam pencils rho0 TB1 TB0 Qc Qt N1 N0 = true`, then for EVERY `t : ℕ`,
EVERY proper set `X` whose points either satisfy `x.2.1 - q0 * x.1 = 0` or lie in some
`P ∈ pencils` at parameter `t`, and EVERY base point `p = (1, q0, c) ∈ X` with
`0 ≤ c ≤ TB1 * t + TB0` and `c % 2 = rho0`, we have:
`projLineCount X (1, q0, c) ≤ 1 + N1 * t + N0`. -/
theorem projLineCount_le_of_certifyTarget
    {q0 : ℤ} {Lam : ℕ} {pencils : List Pencil}
    {rho0 TB1 TB0 Qc Qt N1 N0 : ℕ}
    (hcert : certifyTarget q0 Lam pencils rho0 TB1 TB0 Qc Qt N1 N0 = true)
    {t : ℕ} {X : Finset Pt} (hX : Proper X)
    (hcover : ∀ x ∈ X, x.2.1 - q0 * x.1 = 0 ∨ ∃ P ∈ pencils, P.Mem t x)
    {c : ℤ} (hp : (1, q0, c) ∈ X)
    (hc0 : 0 ≤ c) (hc_hi : c ≤ ((TB1 * t + TB0 : ℕ) : ℤ))
    (hc_par : c % 2 = (rho0 : ℤ)) :
    projLineCount X (1, q0, c) ≤ 1 + N1 * t + N0 := by
  have hhull := hullSum_le_of_certifyTarget hcert hc0 hc_hi hc_par
  unfold certifyTarget certifyHeader at hcert
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, List.all_eq_true] at hcert
  have hLam : 0 < Lam := hcert.1.1.1.1.1.1.1.1
  have hPall := hcert.1.2
  set M := 2 * Lam
  set aps := pencils.map (Pencil.toAff q0 Lam)
  set act := activeList M aps c
  have hM : 0 < M := by omega
  have hMpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  have hact_ne : ∀ entry ∈ act, entry.2 ≠ [] := fun _ h => activeList_ne h
  have hact_mem_aps : ∀ entry ∈ act, ∀ ap ∈ entry.2, ap ∈ aps := fun _ h _ hap =>
    activeList_mem_aps h hap
  let U : Finset (Option ℤ) := (act.toFinset).biUnion fun entry =>
    (Finset.Icc (-listMax (loTerm M entry.1 c (t : ℤ)) entry.2)
                (listMax (hiTerm M entry.1 c (t : ℤ)) entry.2)).image
      (fun k => (some ((M : ℤ) * k + (entry.1 : ℤ)) : Option ℤ))
  let L : Finset (Option ℤ) := insert none U
  refine projLineCount_le_of_label hX hp (zLabel q0 c Lam) L ?_ ?_ ?_
  · have hnonneg : ∀ entry ∈ act, ∀ ap ∈ entry.2, 0 ≤ ap.ht * (t : ℤ) + ap.h0 := by
      intro entry hentry ap hap
      rcases List.mem_map.mp (hact_mem_aps entry hentry ap hap) with ⟨P, _, rfl⟩
      dsimp only [Pencil.toAff]; positivity
    have hU : (U.card : ℤ) ≤ hullSum M act c (t : ℤ) :=
      card_biUnion_active_le hM act c (t : ℤ) hact_ne hnonneg
    have hL : L.card ≤ U.card + 1 := Finset.card_insert_le _ _
    have hLZ : (L.card : ℤ) ≤ 1 + (N1 : ℤ) * (t : ℤ) + (N0 : ℤ) := by omega
    exact_mod_cast hLZ
  · intro x hx
    have hxm : x ∈ X := Finset.mem_of_mem_erase hx
    rcases hcover x hxm with hD0 | ⟨P, hP, hPx⟩
    · have hlab : zLabel q0 c Lam x = none := by simp [zLabel, hD0]
      rw [hlab]; exact Finset.mem_insert_self _ _
    · rcases hPx with ⟨hx1, hx2, hxlo, hxhi, hxpar⟩
      have hPinfo := hPall P hP
      set D : ℤ := P.q - q0 * P.p
      have hDne : D ≠ 0 := hPinfo.1.1.1
      have hDdvd : (Lam : ℤ) % D = 0 := hPinfo.1.1.2
      have hDx : x.2.1 - q0 * x.1 = D := by rw [hx1, hx2]
      set f : ℕ := Lam / D.natAbs
      set sg : ℤ := if 0 < D then 1 else -1
      have hDnat : D.natAbs ∣ Lam := Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero hDdvd)
      have hfD_nat : f * D.natAbs = Lam := Nat.div_mul_cancel hDnat
      have hsgD : sg * (D.natAbs : ℤ) = D := by
        dsimp only [sg]
        split_ifs with hpos
        · rw [one_mul]; exact Int.natAbs_of_nonneg (le_of_lt hpos)
        · have hneg : D ≤ 0 := by omega
          have h1 : (D.natAbs : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hneg
          omega
      have hLam_eq : (Lam : ℤ) = D * (sg * (f : ℤ)) := by
        have h1 : (f : ℤ) * (D.natAbs : ℤ) = (Lam : ℤ) := by exact_mod_cast hfD_nat
        have hsg2 : sg * sg = 1 := by dsimp only [sg]; split_ifs <;> ring
        calc (Lam : ℤ) = (f : ℤ) * (D.natAbs : ℤ) := h1.symm
          _ = (sg * sg) * ((f : ℤ) * (D.natAbs : ℤ)) := by rw [hsg2, one_mul]
          _ = (sg * (D.natAbs : ℤ)) * (sg * (f : ℤ)) := by ring
          _ = D * (sg * (f : ℤ)) := by rw [hsgD]
      set z : ℤ := sg * (f : ℤ) * (x.2.2 - c * P.p)
      have hlab : zLabel q0 c Lam x = some z := by
        unfold zLabel
        dsimp only
        rw [hDx, hx1]
        split_ifs with h0
        · exact absurd h0 hDne
        · congr 1
          have hrew : (Lam : ℤ) * (x.2.2 - c * P.p) = D * z := by rw [hLam_eq]; dsimp only [z]; ring
          rw [hrew, Int.mul_ediv_cancel_left _ hDne]
      rw [hlab]
      refine Finset.mem_insert_of_mem ?_
      set ap := P.toAff q0 Lam
      set σZ : ℤ := z % (M : ℤ)
      set kZ : ℤ := z / (M : ℤ)
      have hσ_nn : 0 ≤ σZ := Int.emod_nonneg z (ne_of_gt hMpos)
      have hσ_lt : σZ < (M : ℤ) := Int.emod_lt_of_pos z hMpos
      set σ : ℕ := σZ.toNat
      have hσ_eq : (σ : ℤ) = σZ := Int.toNat_of_nonneg hσ_nn
      have hσ_ltM : σ < M := by exact_mod_cast (hσ_eq ▸ hσ_lt)
      have hz_decomp : z = (M : ℤ) * kZ + (σ : ℤ) := by
        rw [hσ_eq]; exact (Int.mul_ediv_add_emod z (M : ℤ)).symm
      have hap_act : ap.isActive c σ = true := by
        unfold AffPencil.isActive
        rw [beq_iff_eq]
        have hmu_eq : (ap.mu : ℤ) = 2 * (f : ℤ) := by
          dsimp only [ap, Pencil.toAff]; rw [Nat.cast_mul]; rfl
        have hmu_dvd_M : (ap.mu : ℤ) ∣ (M : ℤ) := by
          have h2dvd : 2 * f ∣ 2 * Lam := Nat.mul_dvd_mul_left 2 (Nat.div_dvd_of_dvd hDnat)
          exact_mod_cast h2dvd
        have hσ_mod_mu : ((σ : ℤ) - (ap.zc * c + ap.z0)) % (ap.mu : ℤ) =
            (z - (ap.zc * c + ap.z0)) % (ap.mu : ℤ) := by
          have h1 : (σ : ℤ) - (ap.zc * c + ap.z0) =
              (z - (ap.zc * c + ap.z0)) - (M : ℤ) * kZ := by omega
          rw [h1, Int.sub_emod]
          have hMk : ((M : ℤ) * kZ) % (ap.mu : ℤ) = 0 :=
            Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left hmu_dvd_M kZ)
          rw [hMk, sub_zero, Int.emod_emod]
        rw [hσ_mod_mu]
        have hdiff : z - (ap.zc * c + ap.z0) = sg * (f : ℤ) * (x.2.2 - P.rho) := by
          dsimp only [z, ap, Pencil.toAff]; ring
        rw [hdiff, hmu_eq]
        have h2dvd : (2 : ℤ) ∣ (x.2.2 - P.rho) := by
          refine Int.dvd_of_emod_eq_zero ?_
          rw [Int.sub_emod, hxpar, sub_self, Int.zero_emod]
        rcases h2dvd with ⟨q2, hq2⟩
        rw [hq2]
        have hrew : sg * (f : ℤ) * (2 * q2) = (2 * (f : ℤ)) * (sg * q2) := by ring
        rw [hrew, Int.mul_emod_right]
      set psσ := aps.filter (fun a => a.isActive c σ)
      have hap_mem_psσ : ap ∈ psσ :=
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨P, hP, rfl⟩, hap_act⟩
      have hpsσ_ne : psσ.isEmpty = false := by
        cases hps : psσ with
        | nil => rw [hps] at hap_mem_psσ; cases hap_mem_psσ
        | cons _ _ => rfl
      have hentry_mem : (σ, psσ) ∈ act := by
        have hf_pos : 0 < f := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hfD_nat; omega)
        have hmu_pos : 0 < ap.mu := Nat.mul_pos (by decide) hf_pos
        have hmu_dvd_M_nat : ap.mu ∣ M := by
          dsimp only [ap, Pencil.toAff, M]
          exact Nat.mul_dvd_mul_left 2 (Nat.div_dvd_of_dvd hDnat)
        have hσ_cand : σ ∈ candSigmas M aps c :=
          mem_candSigmas_of_active (List.mem_map.mpr ⟨P, hP, rfl⟩) hmu_pos hmu_dvd_M_nat
            hσ_ltM hap_act
        simp only [act, activeList, List.mem_filterMap]
        refine ⟨σ, hσ_cand, ?_⟩
        simp only [psσ, hpsσ_ne, Bool.false_eq_true, ↓reduceIte]
      have hz_bounds : ap.lc * c - (ap.ht * (t : ℤ) + ap.h0) ≤ z ∧
          z ≤ ap.lc * c + (ap.ht * (t : ℤ) + ap.h0) := by
        have hf0 : (0 : ℤ) ≤ (f : ℤ) := Int.natCast_nonneg f
        have hmul_lo : (f : ℤ) * (-((P.B1 * t + P.B0 : ℕ) : ℤ)) ≤ (f : ℤ) * x.2.2 :=
          mul_le_mul_of_nonneg_left hxlo hf0
        have hmul_hi : (f : ℤ) * x.2.2 ≤ (f : ℤ) * ((P.B1 * t + P.B0 : ℕ) : ℤ) :=
          mul_le_mul_of_nonneg_left hxhi hf0
        have hsg_cases : sg = 1 ∨ sg = -1 := by dsimp only [sg]; split_ifs <;> simp
        have hlo_z : -(f : ℤ) * ((P.B1 * t + P.B0 : ℕ) : ℤ) ≤ sg * (f : ℤ) * x.2.2 ∧
            sg * (f : ℤ) * x.2.2 ≤ (f : ℤ) * ((P.B1 * t + P.B0 : ℕ) : ℤ) := by
          rcases hsg_cases with hsg1 | hsg1 <;> rw [hsg1]
          · constructor <;> linarith
          · constructor <;> linarith
        have hz_eq : z = ap.lc * c + sg * (f : ℤ) * x.2.2 := by
          dsimp only [z, ap, Pencil.toAff]; ring
        have hh_eq : ap.ht * (t : ℤ) + ap.h0 = (f : ℤ) * ((P.B1 * t + P.B0 : ℕ) : ℤ) := by
          rw [Nat.cast_add, Nat.cast_mul]; dsimp only [ap, Pencil.toAff]; ring
        rw [hz_eq, hh_eq]
        constructor <;> linarith
      have hk_hi : kZ ≤ listMax (hiTerm M σ c (t : ℤ)) psσ := by
        have h1 : kZ ≤ hiTerm M σ c (t : ℤ) ap := by
          unfold hiTerm
          rw [le_ediv_iff_mul_le hMpos]
          linarith
        exact le_trans h1 (le_listMax _ hap_mem_psσ)
      have hk_lo : -listMax (loTerm M σ c (t : ℤ)) psσ ≤ kZ := by
        have h1 : -kZ ≤ loTerm M σ c (t : ℤ) ap := by
          unfold loTerm
          rw [le_ediv_iff_mul_le hMpos]
          linarith
        have h2 := le_trans h1 (le_listMax _ hap_mem_psσ)
        omega
      simp only [U, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image, Finset.mem_Icc]
      refine ⟨(σ, psσ), hentry_mem, kZ, ⟨hk_lo, hk_hi⟩, ?_⟩
      congr 1; exact hz_decomp.symm
  · intro x₁ hx₁ x₂ hx₂ heq
    have hm₁ : x₁ ∈ X := Finset.mem_of_mem_erase hx₁
    have hm₂ : x₂ ∈ X := Finset.mem_of_mem_erase hx₂
    have hdvd_any : ∀ x ∈ X, x.2.1 - q0 * x.1 ≠ 0 → (Lam : ℤ) % (x.2.1 - q0 * x.1) = 0 := by
      intro x hx hne
      rcases hcover x hx with h0 | ⟨P, hP, hx1, hx2, _⟩
      · exact absurd h0 hne
      · rw [hx1, hx2]; exact (hPall P hP).1.1.2
    rw [det_one_left]
    unfold zLabel at heq
    dsimp only at heq
    by_cases h1 : x₁.2.1 - q0 * x₁.1 = 0
    · by_cases h2 : x₂.2.1 - q0 * x₂.1 = 0
      · rw [h1, h2]; ring
      · simp [h1, h2] at heq
    · by_cases h2 : x₂.2.1 - q0 * x₂.1 = 0
      · simp [h1, h2] at heq
      · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at heq
        set D₁ := x₁.2.1 - q0 * x₁.1
        set D₂ := x₂.2.1 - q0 * x₂.1
        have hdiv₁ := hdvd_any x₁ hm₁ h1
        have hdiv₂ := hdvd_any x₂ hm₂ h2
        have hm1 : D₁ * (((Lam : ℤ) * (x₁.2.2 - c * x₁.1)) / D₁) =
            (Lam : ℤ) * (x₁.2.2 - c * x₁.1) :=
          Int.mul_ediv_cancel' (dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hdiv₁) _)
        have hm2 : D₂ * (((Lam : ℤ) * (x₂.2.2 - c * x₂.1)) / D₂) =
            (Lam : ℤ) * (x₂.2.2 - c * x₂.1) :=
          Int.mul_ediv_cancel' (dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hdiv₂) _)
        have hLam_ne : (Lam : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hLam)
        have hscaled : (Lam : ℤ) * (D₁ * (x₂.2.2 - c * x₂.1) - D₂ * (x₁.2.2 - c * x₁.1)) = 0 := by
          calc (Lam : ℤ) * (D₁ * (x₂.2.2 - c * x₂.1) - D₂ * (x₁.2.2 - c * x₁.1))
              = D₁ * ((Lam : ℤ) * (x₂.2.2 - c * x₂.1)) -
                D₂ * ((Lam : ℤ) * (x₁.2.2 - c * x₁.1)) := by ring
            _ = D₁ * (D₂ * (((Lam : ℤ) * (x₂.2.2 - c * x₂.1)) / D₂)) -
                D₂ * (D₁ * (((Lam : ℤ) * (x₁.2.2 - c * x₁.1)) / D₁)) := by rw [hm1, hm2]
            _ = 0 := by rw [heq]; ring
        exact (mul_eq_zero.mp hscaled).resolve_left hLam_ne

end HullCert

end StrongDirac
