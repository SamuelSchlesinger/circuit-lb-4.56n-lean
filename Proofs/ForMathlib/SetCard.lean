/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card

/-!
# Counting a finite set by its fibers

Two `Set.ncard` forms of the familiar `Finset` estimates, upstreaming candidates:

* `Set.ncard_le_mul_ncard_image`: if every fiber of `f` on `s` has at most `n` elements, then
  `s` has at most `n` times as many elements as its image.
* `Set.ncard_le_sum_ncard_fiber`: a set on which a natural-number function takes values below
  `T` has at most as many elements as the sum of its fibers over `0, ..., T - 1`.
-/

@[expose] public section

namespace Set

variable {α β : Type*}

/-- A finite set whose fibers under `f` have at most `n` elements has at most `n` times as many
elements as its image. -/
theorem ncard_le_mul_ncard_image {s : Set α} (hs : s.Finite) (f : α → β) (n : ℕ)
    (h : ∀ b, (s ∩ f ⁻¹' {b}).ncard ≤ n) : s.ncard ≤ n * (f '' s).ncard := by
  classical
  lift s to Finset α using hs
  rw [ncard_coe_finset, ← Finset.coe_image, ncard_coe_finset]
  refine Finset.card_le_mul_card_image s n fun b _ => ?_
  simpa only [← ncard_coe_finset, Finset.coe_filter, preimage_singleton,
    inter_ofPred_eq_sep, Finset.mem_coe] using h b

/-- A finite set on which `f` takes values below `T` is no larger than the sum of its fibers
over `0, ..., T - 1`. -/
theorem ncard_le_sum_ncard_fiber {s : Set α} (hs : s.Finite) (f : α → ℕ) (T : ℕ)
    (hf : ∀ a ∈ s, f a < T) :
    s.ncard ≤ ∑ t ∈ Finset.range T, (s ∩ f ⁻¹' {t}).ncard := by
  lift s to Finset α using hs
  rw [ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range T)
      fun a ha => Finset.mem_range.mpr (hf a ha)]
  simp only [← ncard_coe_finset, Finset.coe_filter, preimage_singleton,
    inter_ofPred_eq_sep, Finset.mem_coe]
  exact le_rfl

end Set
