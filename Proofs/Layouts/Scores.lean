/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Multigraph
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Layouts from scores

Sorting the vertices by a real score gives a layout every prefix of which is a threshold set
of the score (`exists_key_of_score`). Which grid window a threshold falls in is decided by
`exists_grid_index`. Both are used to turn the per-threshold estimates of the Gaussian layouts
into bounds on every prefix cut.
-/

@[expose] public section

namespace Proofs

variable {V : Type*}

/-- Listing the vertices in increasing order of an injective key gives a layout that is
monotone in the key. -/
theorem Layout.exists_monotone [Finite V] {α : Type*} [LinearOrder α] {f : V → α}
    (hf : f.Injective) : ∃ π : Layout V, ∀ v w, f v ≤ f w → π v ≤ π w := by
  let := LinearOrder.lift' f hf
  have := Fintype.ofFinite V
  let e := (Fintype.orderIsoFinOfCardEq V Nat.card_eq_fintype_card.symm).symm
  exact ⟨e.toEquiv, fun v w h => e.monotone h⟩

/-- A real number in `[a, a + M δ)` lies in one of the `M` grid windows
`[a + i δ, a + (i + 1) δ)`. -/
theorem exists_grid_index {a δ m : ℝ} (hδ : 0 < δ) {M : ℕ} (hlo : a ≤ m)
    (hhi : m < a + M * δ) : ∃ i < M, a + i * δ ≤ m ∧ m < a + (i + 1) * δ := by
  have hdiv : 0 ≤ (m - a) / δ := div_nonneg (by linarith) hδ.le
  have ht : a + ⌊(m - a) / δ⌋₊ * δ ≤ m := by
    have := (le_div_iff₀ hδ).mp (Nat.floor_le hdiv); linarith
  have ht' : m < a + (⌊(m - a) / δ⌋₊ + 1) * δ := by
    have := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((m - a) / δ)); linarith
  refine ⟨⌊(m - a) / δ⌋₊, ?_, ht, ht'⟩
  by_contra! h
  have : (M : ℝ) * δ ≤ ⌊(m - a) / δ⌋₊ * δ := by gcongr
  linarith

/-- **Sorting by a score.** Ties broken by a fixed enumeration, the vertices get an injective
key every prefix `{v | key v < t}` of which is a threshold set: it is empty, or some `m` is at
least every score inside it and at most every score outside it. -/
theorem exists_key_of_score [Finite V] (score : V → ℝ) :
    ∃ key : V → ℕ, Function.Injective key ∧ ∀ t : ℕ, (∀ v, ¬ key v < t) ∨
      ∃ m : ℝ, (∀ v, key v < t → score v ≤ m) ∧ ∀ v, ¬ key v < t → m ≤ score v := by
  have := Fintype.ofFinite V
  let rank (v : V) : ℝ ×ₗ ℕ := toLex (score v, (Fintype.equivFin V v : ℕ))
  have hrank : Function.Injective rank := fun v w h =>
    (Fintype.equivFin V).injective (Fin.ext (congrArg (fun x => (ofLex x).2) h))
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hrank
  refine ⟨fun v => π v, fun v w h => π.injective (Fin.ext h), fun t => ?_⟩
  have hmono (u : V) (hu : (π u : ℕ) < t) (v : V) (hv : ¬ (π v : ℕ) < t) :
      score u ≤ score v := by
    by_contra! h
    have hrev : rank v ≤ rank u := le_of_lt (Prod.Lex.lt_iff.mpr (Or.inl h))
    exact hv (Nat.lt_of_le_of_lt (hπ v u hrev) hu)
  by_cases hne : (Finset.univ.filter fun v => (π v : ℕ) < t).Nonempty
  · obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image _ score hne
    rw [Finset.mem_filter] at hu₀
    exact Or.inr ⟨score u₀, fun v hv => hmax v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩),
      fun v hv => hmono u₀ hu₀.2 v hv⟩
  · exact Or.inl fun v hv => hne ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩

end Proofs
