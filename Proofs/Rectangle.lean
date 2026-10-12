/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Rectangle-free sets

An *input* is a function `x : ι → U` from a type of coordinates to an alphabet. A set of
coordinates `X` cuts an input into two *parts*: its restriction to `X` and its restriction
to the complement `X^c`. `Statement.lean` defines the *rectangle* `rectangle X A B` as the set
of inputs whose part on `X` lies in `A` and whose part on `X^c` lies in `B`, and calls a set
`K`-*rectangle-free* when every rectangle inside it, for every cut, has a side with fewer than
`K` elements. This is the combinatorial property of the hard function used by the worst-case
proof; `CircuitLowerBound` separately assumes
`log |S_n| = n log |U| - o(n)`.

Besides the definition itself, the proof uses the *support lemma*
`RectangleFree.pow_ncard_compl_lt`: a large rectangle-free set depends on all but fewer than
`log_|U| K` coordinates. Indeed, if `S` ignored a set `D` of `log_|U| K` coordinates, then `S`
would contain the rectangle whose side on `D` is everything, so its other side, and hence `S`,
would be small.

The average-case lower bounds use a quantitative form of rectangle-freeness: `S` has *bias*
at most `b` (`RectangleBias`) when on every rectangle with two large sides, its density is
within `b` of `1/2`. Then the inputs of the rectangle in `S` and those outside `S` differ in
number by at most a `2 b` fraction (`signedCount`).

## Main results

* `Proofs.exists_thick_or_ncard_lt`: a set that ignores the coordinates outside `R`, where
  those carry at least `K` assignments, is a rectangle with both sides of size at least `K` or
  has fewer than `|U| K ^ 2` elements.
* `Proofs.RectangleFree.pow_ncard_compl_lt`: the support lemma.
* `Proofs.RectangleBias.abs_signedCount_le_of_dependsOn`: the same dichotomy for biased sets.
-/

@[expose] public section

namespace Proofs

open Set

variable {ι U : Type*}

/-- An input is determined by its two parts. -/
theorem eq_of_domRestrict_eq {X : Set ι} {x y : ι → U}
    (h₁ : X.domRestrict x = X.domRestrict y) (h₂ : Xᶜ.domRestrict x = Xᶜ.domRestrict y) :
    x = y := by
  funext i
  grind [domRestrict_eq_domRestrict_iff, Set.EqOn]

/-- Splitting an input into its two parts is injective. -/
theorem domRestrict_prod_injective (X : Set ι) :
    Function.Injective fun x : ι → U => (X.domRestrict x, Xᶜ.domRestrict x) :=
  fun _ _ h => eq_of_domRestrict_eq (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2

/-- A rectangle-free set has a positive threshold, even when it is empty. -/
theorem RectangleFree.pos {S : Set (ι → U)} {K : ℕ} (h : RectangleFree S K) : 0 < K := by
  simpa using h univ ∅ ∅ fun _ hx => absurd hx.1 (notMem_empty _)

/-- A set that does not depend on the coordinates in `D` is the rectangle whose side on `D` is
every assignment and whose side on `D^c` is the set of its parts there. -/
theorem eq_rectangle_of_dependsOn {T : Set (ι → U)} {D : Set ι} (hD : DependsOn (· ∈ T) Dᶜ) :
    T = rectangle D univ (Dᶜ.domRestrict '' T) := by
  refine subset_antisymm (fun x hx => ⟨mem_univ _, x, hx, rfl⟩) ?_
  rintro z ⟨-, y, hy, hyz⟩
  have : (y ∈ T) = (z ∈ T) := hD fun i hi => congrFun hyz ⟨i, hi⟩
  exact this ▸ hy

section Finite

variable [Finite ι] [Finite U]

/-- Over finite coordinates and alphabets, the sides of a rectangle are finite and the
rectangle-free condition reads in terms of `ncard`. -/
theorem RectangleFree.ncard_lt_or {S : Set (ι → U)} {K : ℕ} (hS : RectangleFree S K)
    (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) (hAB : rectangle X A B ⊆ S) :
    A.ncard < K ∨ B.ncard < K := by
  rcases hS X A B hAB with h | h
  · rw [← A.toFinite.cast_ncard_eq] at h
    exact Or.inl (by exact_mod_cast h)
  · rw [← B.toFinite.cast_ncard_eq] at h
    exact Or.inr (by exact_mod_cast h)

/-- **Thick or small.** Let `T` depend only on the coordinates in `R`, and let the other
coordinates carry at least `K ≥ 1` assignments. Then `T` is a rectangle with both sides of size
at least `K`, or `T` has fewer than `|U| K ^ 2` elements.

Take a smallest set `D` of ignored coordinates carrying at least `K` assignments, so that
`|U| ^ |D| ≤ |U| (K - 1)`. Then `T` is the rectangle whose side on `D` is everything; if its
other side has fewer than `K` elements, `T` has at most `|U| ^ |D| (K - 1)` of them. -/
theorem exists_thick_or_ncard_lt [Nonempty U] {T : Set (ι → U)} {R : Set ι}
    (hR : DependsOn (· ∈ T) R) {K : ℕ} (hK : 1 ≤ K) (hle : K ≤ Nat.card U ^ Rᶜ.ncard) :
    (∃ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
      T = rectangle X A B ∧ K ≤ A.ncard ∧ K ≤ B.ncard) ∨ T.ncard < Nat.card U * K ^ 2 := by
  have hq : 0 < Nat.card U := Nat.card_pos
  have hex : ∃ d, K ≤ Nat.card U ^ d := ⟨_, hle⟩
  obtain ⟨d, hdK, hdmin⟩ : ∃ d, K ≤ Nat.card U ^ d ∧ ∀ d' < d, Nat.card U ^ d' < K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun d' hd' => not_le.mp (Nat.find_min hex hd')⟩
  have hdR : d ≤ Rᶜ.ncard := by
    by_contra! h
    exact absurd hle (not_le.mpr (hdmin _ h))
  obtain ⟨D, hDR, rfl⟩ := exists_subset_card_eq hdR
  set B : Set (↥Dᶜ → U) := Dᶜ.domRestrict '' T
  have hT : T = rectangle D univ B := eq_rectangle_of_dependsOn (hR.mono (subset_compl_comm.mp hDR))
  have hA : (univ : Set (D → U)).ncard = Nat.card U ^ D.ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
  by_cases hB : K ≤ B.ncard
  · exact Or.inl ⟨D, univ, B, hT, hA ▸ hdK, hB⟩
  refine Or.inr ?_
  have hcard : T.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := by
    calc T.ncard
        ≤ ((univ : Set (D → U)) ×ˢ B).ncard :=
          ncard_le_ncard_of_injOn _ (fun x hx => ⟨mem_univ _, x, hx, rfl⟩)
            (domRestrict_prod_injective D).injOn
      _ = Nat.card U ^ D.ncard * B.ncard := by rw [ncard_prod, hA]
      _ ≤ Nat.card U ^ D.ncard * (K - 1) := Nat.mul_le_mul_left _ (by lia)
  -- Minimality of `|D|` gives `|U| ^ |D| ≤ |U| (K - 1)` once `D` is nonempty.
  rcases Nat.eq_zero_or_pos D.ncard with hd | hd
  · rw [hd, pow_zero, one_mul] at hcard
    calc T.ncard ≤ K - 1 := hcard
      _ < K := by lia
      _ ≤ Nat.card U * K ^ 2 :=
          (Nat.le_self_pow two_ne_zero K).trans (Nat.le_mul_of_pos_left _ hq)
  · have hlt : Nat.card U ^ (D.ncard - 1) < K := hdmin _ (by lia)
    have hpow : Nat.card U ^ D.ncard = Nat.card U * Nat.card U ^ (D.ncard - 1) := by
      rw [← pow_succ']; congr 1; lia
    calc T.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := hcard
      _ ≤ Nat.card U * (K - 1) * (K - 1) := by rw [hpow]; gcongr; lia
      _ < Nat.card U * K ^ 2 := by
          rw [mul_assoc, sq]
          exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' (by lia) (by lia)) hq

/-- **The support lemma.** A rectangle-free set with at least `|U| K ^ 2` elements depends on
all but fewer than `log_|U| K` coordinates: if `S` depends only on the coordinates in `R`,
then `|U| ^ |R^c| < K`. -/
theorem RectangleFree.pow_ncard_compl_lt [Nonempty U] {S : Set (ι → U)} {K : ℕ}
    (hS : RectangleFree S K) {R : Set ι} (hR : DependsOn (· ∈ S) R)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ Rᶜ.ncard < K := by
  by_contra! hle
  rcases exists_thick_or_ncard_lt hR hS.pos hle with ⟨X, A, B, hSAB, hA, hB⟩ | h
  · rcases hS.ncard_lt_or X A B hSAB.symm.subset with h | h <;> lia
  · lia

/-! ### Bias -/

/-- The number of inputs of `R` in `S` minus the number of inputs of `R` outside `S`. -/
noncomputable def signedCount (S R : Set (ι → U)) : ℝ :=
  ((R ∩ S).ncard : ℝ) - (R \ S).ncard

theorem signedCount_add_ncard (S R : Set (ι → U)) :
    ((R ∩ S).ncard : ℝ) + (R \ S).ncard = R.ncard := by
  exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard R S

theorem abs_signedCount_le (S R : Set (ι → U)) : |signedCount S R| ≤ R.ncard := by
  have := signedCount_add_ncard S R
  rw [signedCount, abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (R ∩ S).ncard,
    Nat.cast_nonneg (α := ℝ) (R \ S).ncard]

/-- Signed counts add over a set and its complement in a larger set. -/
theorem signedCount_sdiff (S : Set (ι → U)) {R D : Set (ι → U)} (h : R ⊆ D) :
    signedCount S D = signedCount S R + signedCount S (D \ R) := by
  have hsplit (P : Set (ι → U)) : D ∩ P = (R ∩ P) ∪ ((D \ R) ∩ P) := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_sdiff]
    have := @h x
    tauto
  have hdisj (P : Set (ι → U)) : Disjoint (R ∩ P) ((D \ R) ∩ P) :=
    disjoint_left.mpr fun x hx hx' => hx'.1.2 hx.1
  have hi := ncard_union_eq (hdisj S)
  have hd := ncard_union_eq (hdisj Sᶜ)
  rw [← hsplit] at hi hd
  simp only [← sdiff_eq] at hd
  rw [signedCount, signedCount, signedCount, hi, hd]
  push_cast
  ring

/-- The signed count is twice the deviation of `|R ∩ S|` from `|R| / 2`. -/
theorem signedCount_eq (S R : Set (ι → U)) :
    signedCount S R = 2 * (((R ∩ S).ncard : ℝ) - R.ncard / 2) := by
  have := signedCount_add_ncard S R
  rw [signedCount]
  linarith

/-- On a rectangle with both sides of size at least `K`, a set with bias at most `b` has signed
count at most `2 b` times the size of the rectangle. -/
theorem RectangleBias.abs_signedCount_rectangle_le {S : Set (ι → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) {X : Set ι} {A : Set (X → U)} {B : Set (↥Xᶜ → U)}
    (hA : K ≤ A.ncard) (hB : K ≤ B.ncard) :
    |signedCount S (rectangle X A B)| ≤ 2 * b * (rectangle X A B).ncard := by
  rw [signedCount_eq, abs_mul, abs_two]
  linarith [hS X A B hA hB]

/-- A bias bound is nonnegative once half of the coordinates carry at least `K` assignments:
the whole input space is then a rectangle with both sides of size at least `K`. -/
theorem RectangleBias.nonneg [Nonempty U] {S : Set (ι → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hK : K ≤ Nat.card U ^ (Nat.card ι / 2)) : 0 ≤ b := by
  obtain ⟨X, -, hX⟩ := exists_subset_card_eq (s := (univ : Set ι)) (n := Nat.card ι / 2)
    (by rw [ncard_univ]; exact Nat.div_le_self _ _)
  have hXc : Nat.card ι / 2 ≤ Xᶜ.ncard := by
    have := ncard_add_ncard_compl X
    lia
  have hA : K ≤ (univ : Set (X → U)).ncard := by
    rwa [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hX]
  have hB : K ≤ (univ : Set (↥Xᶜ → U)).ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
    exact hK.trans (Nat.pow_le_pow_right Nat.card_pos hXc)
  have hR : (0 : ℝ) < (rectangle X (univ : Set (X → U)) univ).ncard := by
    rw [show rectangle X (univ : Set (X → U)) univ = univ by ext; simp [rectangle], ncard_univ]
    exact_mod_cast Nat.card_pos
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hS X univ univ hA hB)) hR

/-- **Bias on a set that ignores many coordinates.** If `T` depends only on the coordinates in
`R` and the others carry at least `K` assignments, then either `T` is a large rectangle, on
which `S` has bias at most `b`, or `T` is small. -/
theorem RectangleBias.abs_signedCount_le_of_dependsOn [Nonempty U] {S : Set (ι → U)} {K : ℕ}
    {b : ℝ} (hS : RectangleBias S K b) (hb : 0 ≤ b) {T : Set (ι → U)} {R : Set ι}
    (hR : DependsOn (· ∈ T) R) (hK : 1 ≤ K) (hle : K ≤ Nat.card U ^ Rᶜ.ncard) :
    |signedCount S T| ≤ 2 * b * T.ncard + (Nat.card U * K ^ 2 : ℕ) := by
  rcases exists_thick_or_ncard_lt hR hK hle with ⟨X, A, B, rfl, hA, hB⟩ | h
  · exact (hS.abs_signedCount_rectangle_le hA hB).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · have : (T.ncard : ℝ) ≤ (Nat.card U * K ^ 2 : ℕ) := by exact_mod_cast h.le
    linarith [abs_signedCount_le S T, mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b)
      (Nat.cast_nonneg (α := ℝ) T.ncard)]

end Finite

/-- A bias bound for rectangles with sides of size at least `K` holds for larger sides. -/
theorem RectangleBias.mono {S : Set (ι → U)} {K K' : ℕ} {b : ℝ} (h : RectangleBias S K b)
    (hK : K ≤ K') : RectangleBias S K' b :=
  fun X A B hA hB => h X A B (hK.trans hA) (hK.trans hB)

end Proofs
