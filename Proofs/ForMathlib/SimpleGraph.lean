/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cuts of simple graphs

`SimpleGraph.cutFinset S` is the set of edges of a finite simple graph with exactly one endpoint
in `S`. An upstreaming candidate.
-/

@[expose] public section

namespace SimpleGraph

variable {W : Type*} (H : SimpleGraph W) [Fintype H.edgeSet]

open Classical in
/-- The edges of a simple graph with exactly one endpoint in `S`. -/
noncomputable def cutFinset (S : Finset W) : Finset (Sym2 W) :=
  H.edgeFinset.filter fun e => ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S

variable {H}

theorem mem_cutFinset {S : Finset W} {e : Sym2 W} :
    e ∈ H.cutFinset S ↔ e ∈ H.edgeSet ∧ ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S := by
  simp [cutFinset, mem_edgeFinset]

/-- An edge crosses `S` exactly when it is an edge with one endpoint on each side. -/
theorem mem_cutFinset_mk {S : Finset W} {a b : W} :
    s(a, b) ∈ H.cutFinset S ↔ H.Adj a b ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)) := by
  rw [mem_cutFinset, mem_edgeSet]
  grind [Sym2.eq_iff]

theorem cutFinset_subset_edgeFinset (S : Finset W) : H.cutFinset S ⊆ H.edgeFinset :=
  fun _ he => mem_edgeFinset.mpr (mem_cutFinset.mp he).1

end SimpleGraph
