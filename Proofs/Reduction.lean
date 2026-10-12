/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Compiler

/-!
# From small circuits to wide graphs

This file combines three ingredients of the lower-bound proof for a single input length:

* compiling a circuit into a constraint network (`Proofs.Compiler`),
* the width demand for networks (`Proofs.Network.logb_ncard_accepted_le`), and
* the support lemma for rectangle-free sets (`Proofs.RectangleFree.pow_ncard_compl_lt`).

**The reduction theorem** (`Proofs.exists_graph_of_decides`). Let `c` be a circuit with `s`
inner gates (gates of positive arity; constants are free) of fan-in at most `r ≥ 2`, over any
basis on a finite alphabet `U` with `q ≥ 2` symbols, that decides a `K`-rectangle-free set
`S ⊆ U^n` with `|S| ≥ q K^2`. Then there is a connected multigraph `G` of maximum
degree `r + 1` with at most `2 r s + 3` vertices and cycle rank

`β₁(G) ≤ (r - 1) s - n + log_q K + 1`,

every layout of which has width at least

`log_q |S| - 3 log_q K - log_q (|V(G)| + 1) - (r + 2)`.

For fan-in two the graph is subcubic, `β₁(G) ≤ s - n + log_q K + 1`, and the width is at least
`log_q |S| - 3 log_q K - log_q (|V(G)| + 1) - 4`.

The graph is the constraint graph of `c`. The cycle rank bound is the count of the compiler,
together with the support lemma, which says that `c` reads all but `log_q K` of its inputs.
The width bound is the rectangle bound for the read-once branching program of a layout
(`Proofs.Network.ncard_accepted_le`), in which the unread inputs contribute fewer than `K`
edges, again by the support lemma.

For a dense set, `log_q |S| ≈ n`; so a small circuit gives a graph whose cycle rank is about
`(r - 1) s - n` but whose layouts all have width about `n`.
-/

@[expose] public section

namespace Proofs

open Cslib.Circuits Set

variable {U : Type*} {σ : Signature} {n : ℕ}

/-- The constraint network of a one-output circuit. -/
noncomputable abbrev constraintNetwork (I : Interpretation σ U) (Acc : Set U)
    (c : Circuit σ n 1) :=
  Compiler.network c.program c.outputs I fun _ => Acc

/-- The constraint network of a circuit deciding `S` accepts exactly `S`. -/
theorem accepted_constraintNetwork {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ n 1}
    {S : Set (Fin n → U)} (hS : Decides c I Acc S) : (constraintNetwork I Acc c).accepted = S := by
  rw [Compiler.accepted_network]
  ext x
  rw [hS x]
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

section Reduction

variable [Finite U] [Nontrivial U] {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ n 1}
  {S : Set (Fin n → U)} {K r : ℕ}

/-- **The support lemma, for circuits.** A circuit deciding a large rectangle-free set reads all
but fewer than `log_q K` of its inputs. -/
theorem pow_ncard_unread_lt (hS : Decides c I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ (constraintNetwork I Acc c).readᶜ.ncard < K := by
  rw [← accepted_constraintNetwork hS] at hfree hbig
  exact hfree.pow_ncard_compl_lt (constraintNetwork I Acc c).dependsOn_read hbig

/-- **The cycle rank of the constraint graph** is at most `(r - 1) s - n + log_q K + 1` for
fan-in at most `r`, where `s` counts the inner gates, when the unread inputs carry fewer than
`K` assignments. -/
theorem cycleRank_le (hfan : c.FanInAtMost r)
    (hunread : Nat.card U ^ (constraintNetwork I Acc c).readᶜ.ncard < K) :
    ((constraintNetwork I Acc c).cycleRank : ℝ) ≤
      ((r - 1) * c.innerSize : ℕ) - n + Real.logb (Nat.card U) K + 1 := by
  set N := constraintNetwork I Acc c
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hrank := Compiler.cycleRank_add_ncard_read_le (out := c.outputs) I (fun _ => Acc) hfan
    (Compiler.connected I _)
  have hunread : (N.readᶜ.ncard : ℝ) < Real.logb (Nat.card U) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast (Nat.zero_lt_of_lt hunread)),
      Real.rpow_natCast]
    exact_mod_cast hunread
  have hcompl : N.readᶜ.ncard + N.read.ncard = n := by
    rw [add_comm, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have : (N.cycleRank : ℝ) + N.read.ncard ≤ ((r - 1) * c.innerSize : ℕ) + 1 := by
    exact_mod_cast hrank
  have : (N.readᶜ.ncard : ℝ) + N.read.ncard = n := by exact_mod_cast hcompl
  linarith

/-- **Every layout of the constraint graph is wide.** For fan-in at most `r ≥ 2`, if all
frontiers of a layout have at most `w` edges, then
`log_q |S| ≤ w + (r + 2) + 3 log_q K + log_q (|V| + 1)`. -/
theorem logb_ncard_le (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : Decides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard)
    (π : Layout (Compiler.Vertex c.program c.outputs)) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I Acc c).cut (π.initial t)).ncard ≤ w) :
    Real.logb (Nat.card U) S.ncard ≤
      w + (r + 2) + 3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (Nat.card (Compiler.Vertex c.program c.outputs) + 1) := by
  have hacc := accepted_constraintNetwork hS
  have h := (constraintNetwork I Acc c).logb_ncard_accepted_le (hacc ▸ hfree)
    (hacc ▸ hbig) π hw (Compiler.maxDegreeLE I _ hr hfan) (Compiler.ncard_readAt_le I _)
  rw [hacc] at h
  convert h using 1
  push_cast
  ring

/-- **The reduction theorem.** A circuit with `s` inner gates of fan-in at most `r ≥ 2`, over
any basis on `U`, deciding a `K`-rectangle-free set `S ⊆ U^n` with `|S| ≥ q K^2`, yields a
connected multigraph of maximum degree `r + 1` with at most `2 r s + 3` vertices and cycle rank
at most `(r - 1) s - n + log_q K + 1`, every layout of which has width at least
`log_q |S| - 3 log_q K - log_q (|V| + 1) - (r + 2)`. -/
theorem exists_graph_of_decides (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : Decides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 ∧
      (G.cycleRank : ℝ) ≤ ((r - 1) * c.innerSize : ℕ) - n + Real.logb (Nat.card U) K + 1 ∧
      ∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) S.ncard ≤
          w + (r + 2) + 3 * Real.logb (Nat.card U) K +
            Real.logb (Nat.card U) (Nat.card V + 1) :=
  ⟨_, _, inferInstance, inferInstance, (constraintNetwork I Acc c).toMultigraph,
    Compiler.connected I _, Compiler.maxDegreeLE I _ hr hfan,
    by simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan,
    cycleRank_le hfan (pow_ncard_unread_lt hS hfree hbig),
    fun π _ hw => logb_ncard_le hr hfan hS hfree hbig π hw⟩

end Reduction

end Proofs
