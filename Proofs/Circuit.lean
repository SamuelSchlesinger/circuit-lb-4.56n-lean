/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement

/-!
# Basic facts about circuit lower-bound statements

`Circuit.innerSize_le_size` transfers an inner-gate lower bound to the usual circuit size.
`CircuitLowerBound.mono` and `AverageCaseBound.mono` weaken a coefficient, for example to a
convenient rational bound.
Both definitions are in `Statement.lean`.
-/

@[expose] public section

namespace Cslib.Circuits

/-- Counting only gates of positive arity gives at most the usual circuit size. -/
theorem Circuit.innerSize_le_size {σ : Signature} {n m : ℕ} (c : Circuit σ n m) :
    c.innerSize ≤ c.size := by
  unfold Circuit.innerSize Program.innerGates
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

end Cslib.Circuits

namespace Proofs

open Filter

/-- A circuit lower bound implies every smaller coefficient. -/
theorem CircuitLowerBound.mono {L L' : ℝ} (h : CircuitLowerBound L) (hLL' : L' ≤ L) :
    CircuitLowerBound L' := by
  intro U _ _ S K hfree hK hdense ε hε
  filter_upwards [h U S K hfree hK hdense ε hε] with n hn
  intro σ I Acc c hfan hS
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (sub_le_sub_right hLL' ε)
    (Nat.cast_nonneg n)) (hn σ I Acc c hfan hS)

/-- An average-case bound implies every smaller coefficient. -/
theorem AverageCaseBound.mono {L L' : ℝ} (h : AverageCaseBound L) (hLL' : L' ≤ L) :
    AverageCaseBound L' := by
  intro ε hε
  obtain ⟨γ, hγ, H⟩ := h ε hε
  refine ⟨γ, hγ, ?_⟩
  intro U _ _ S K b hbias hK
  exact (H U S K b hbias hK).mono fun n hn σ I Acc c hfan hs =>
    hn σ I Acc c hfan
      (hs.trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hLL' ε) (Nat.cast_nonneg n)))

end Proofs
