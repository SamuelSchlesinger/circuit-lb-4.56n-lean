/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Compiler.Network

/-!
# Counting the compiler graph

Consumer and signal counts bound edges, vertices, and cycle rank in terms of reachable
inputs and gates of positive arity. Constants are free in the resulting lower bound.
-/

@[expose] public section

namespace Proofs.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} {p : Program σ n s} {out : O → Wire n s}

/-! ### Signals and inner gates -/

/-- Signals are reachable inputs and reachable gates. -/
def signalEquiv :
    Signal p out ≃
      {i : Fin n // Reach p out (.input i)} ⊕ {g : Fin s // Reach p out (.gate g)} where
  toFun
    | ⟨.input i, h⟩ => .inl ⟨i, h⟩
    | ⟨.gate g, h⟩ => .inr ⟨g, h⟩
  invFun
    | .inl i => ⟨.input i.1, i.2⟩
    | .inr g => ⟨.gate g.1, g.2⟩
  left_inv w := by rcases w with ⟨w | w, h⟩ <;> rfl
  right_inv w := by rcases w with w | w <;> rfl

variable (p out) in
/-- The reachable inner gates: reachable gates of positive arity. -/
abbrev InnerGate : Type :=
  {g : Fin s // Reach p out (.gate g) ∧ σ.Arity (p.lines g).op ≠ 0}

/-- The reachable inner gates are among the inner gates. -/
theorem card_innerGate_le : Nat.card (InnerGate p out) ≤ p.innerGates.card := by
  calc Nat.card (InnerGate p out)
      ≤ Nat.card p.innerGates :=
        Nat.card_le_card_of_injective (fun g => ⟨g.1, by simpa [Program.innerGates] using g.2.2⟩)
          fun _ _ h => Subtype.ext (by simpa using h)
    _ = p.innerGates.card := Nat.card_eq_finsetCard _

/-- There are at most `r` slots per reachable inner gate; constant gates have none. -/
theorem card_slot_le {r : ℕ} (hfan : p.FanInAtMost r) :
    Nat.card (Slot p out) ≤ r * Nat.card (InnerGate p out) := by
  calc Nat.card (Slot p out)
      ≤ Nat.card (InnerGate p out × Fin r) := by
        refine Nat.card_le_card_of_injective
          (fun t => (⟨t.1.1, t.2, Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt t.1.2.isLt)⟩,
            ⟨t.1.2.val, t.1.2.isLt.trans_le (hfan.arity_le t.1.1)⟩)) ?_
        rintro ⟨⟨g, a⟩, hg⟩ ⟨⟨g', a'⟩, hg'⟩ h
        grind [Sigma.ext_iff, Fin.ext_iff]
    _ = r * Nat.card (InnerGate p out) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, mul_comm]

/-- There are at least as many reachable gates as reachable inner gates. -/
theorem card_innerGate_le_card_gate :
    Nat.card (InnerGate p out) ≤ Nat.card {g : Fin s // Reach p out (.gate g)} :=
  Nat.card_le_card_of_injective (fun g => ⟨g.1, g.2.1⟩) fun _ _ h =>
    Subtype.ext (by simpa using h)

/-! ### Counting the network -/

variable [Finite O] {U : Type*} (I : Interpretation σ U) (Acc : O → Set U)

/-- The inputs read by the network are the reachable inputs. -/
theorem read_network : (network p out I Acc).read = {i | Reach p out (.input i)} := by
  ext i
  simp only [Network.read, Network.readIn, mem_univ, true_and, mem_ofPred_eq, network]
  constructor
  · rintro ⟨v, hv⟩; exact (site_eq_some hv).1
  · exact fun hi => ⟨_, site_of_reach hi⟩

/-- Each vertex reads at most one input. -/
theorem ncard_readAt_le (v : Vertex p out) : ((network p out I Acc).readAt v).ncard ≤ 1 := by
  refine (ncard_le_one (toFinite _)).mpr ?_
  intro i hi j hj
  grind [site_eq_some hi, site_eq_some hj]

/-- There are two edges per consumer: the feed and the deliver edge of its junction. -/
theorem card_edge : Nat.card (Edge p out) = 2 * Nat.card (Consumer p out) := by
  rw [Nat.card_congr Edge.equiv, Nat.card_sum, Nat.card_congr (junctionEquiv p out), two_mul]

/-- There is a vertex per signal, per consumer, and per output. -/
theorem card_vertex :
    Nat.card (Vertex p out) = Nat.card (Signal p out) + Nat.card (Consumer p out) + Nat.card O := by
  rw [Nat.card_congr Vertex.equiv, Nat.card_sum, Nat.card_sum, Nat.card_congr (junctionEquiv p out),
    add_assoc]

/-- The consumers are the slots and the outputs. -/
theorem card_consumer : Nat.card (Consumer p out) = Nat.card (Slot p out) + Nat.card O :=
  Nat.card_sum

/-- Every signal has a consumer, so there are at least as many consumers as signals. -/
theorem card_signal_le_card_consumer : Nat.card (Signal p out) ≤ Nat.card (Consumer p out) := by
  rw [← Nat.card_congr (junctionEquiv p out)]
  exact Nat.card_le_card_of_injective (fun w => ⟨w, ⟨0, fanout_pos w⟩⟩) fun w w' h =>
    congrArg Sigma.fst h

/-- **The edge count.** For fan-in at most `r`, the edges of the network and the inputs it reads
number at most `(r - 1) s` more than its vertices, where `s` counts the inner gates. -/
theorem card_edge_add_ncard_read_le {r : ℕ} (hfan : p.FanInAtMost r) :
    Nat.card (Edge p out) + (network p out I Acc).read.ncard ≤
      Nat.card (Vertex p out) + (r - 1) * p.innerGates.card := by
  have hread :
      (network p out I Acc).read.ncard = Nat.card {i : Fin n // Reach p out (.input i)} := by
    rw [read_network, ← Nat.card_coe_set_eq]; rfl
  have hsig := Nat.card_congr (signalEquiv (p := p) (out := out))
  rw [Nat.card_sum] at hsig
  have hcons := card_consumer (p := p) (out := out)
  have hslot := card_slot_le (out := out) hfan
  have hinner := card_innerGate_le_card_gate (p := p) (out := out)
  -- `r G ≤ (r - 1) G + G`, for `G` the number of reachable inner gates.
  have hr : r * Nat.card (InnerGate p out) ≤
      (r - 1) * Nat.card (InnerGate p out) + Nat.card (InnerGate p out) := by
    rcases r with _ | r
    · simp
    · simp [add_mul]
  have hrs := Nat.mul_le_mul_left (r - 1) (card_innerGate_le (p := p) (out := out))
  rw [hread, card_edge, card_vertex]
  lia

/-- **The cycle rank.** For fan-in at most `r`, if the network is connected, its cycle rank and
the number of inputs it reads add up to at most `(r - 1) s + 1`, where `s` counts the inner
gates. For fan-in two, the cycle rank is at most `s + 1 - m` for `m` reachable inputs. -/
theorem cycleRank_add_ncard_read_le {r : ℕ} (hfan : p.FanInAtMost r)
    (hconn : (network p out I Acc).Connected) :
    (network p out I Acc).cycleRank + (network p out I Acc).read.ncard ≤
      (r - 1) * p.innerGates.card + 1 := by
  have h := card_edge_add_ncard_read_le (out := out) I Acc hfan
  have hV : Nat.card (Vertex p out) ≤ Nat.card (Edge p out) + 1 := hconn.card_vertex_le
  unfold Multigraph.cycleRank
  lia

/-- **The number of vertices** is at most `2 r s + 3 |O|` for fan-in at most `r`, where `s`
counts the inner gates. -/
theorem card_vertex_le {r : ℕ} (hfan : p.FanInAtMost r) :
    Nat.card (Vertex p out) ≤ 2 * r * p.innerGates.card + 3 * Nat.card O := by
  have hcons := card_consumer (p := p) (out := out)
  have hslot := card_slot_le (out := out) hfan
  have := card_signal_le_card_consumer (p := p) (out := out)
  have hrs : r * Nat.card (InnerGate p out) ≤ r * p.innerGates.card :=
    Nat.mul_le_mul_left r (card_innerGate_le (p := p) (out := out))
  rw [card_vertex, mul_assoc]
  lia

end Proofs.Compiler
