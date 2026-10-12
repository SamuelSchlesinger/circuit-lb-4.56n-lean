/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.ForCslib.Program
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith

/-!
# The compiler graph

Reachable signals are routed through chains of junctions, one per consumer.
This module defines the vertices and edges; `Compiler.Network` supplies their constraints.
-/

@[expose] public section

namespace Proofs.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} (p : Program σ n s) (out : O → Wire n s)

/-! ### Signals, consumers, and junctions -/

/-- A wire is *reachable* when it is upstream of an output: an output itself, or an argument of
a reachable gate. -/
def Reach (w : Wire n s) : Prop :=
  ∃ o, p.Upstream (out o) w

variable {p out}

/-- The outputs are reachable. -/
theorem Reach.output (o : O) : Reach p out (out o) :=
  ⟨o, .refl⟩

/-- The arguments of a reachable gate are reachable. -/
theorem Reach.arg {g : Fin s} (a : Fin (σ.Arity (p.lines g).op)) (h : Reach p out (.gate g)) :
    Reach p out ((p.lines g).wires a) :=
  let ⟨o, ho⟩ := h
  ⟨o, .arg a ho⟩

variable (p out)

/-- The *signals*: the reachable wires. -/
abbrev Signal : Type :=
  {w : Wire n s // Reach p out w}

/-- An argument slot of a reachable gate. -/
abbrev Slot : Type :=
  {t : Σ g : Fin s, Fin (σ.Arity (p.lines g).op) // Reach p out (.gate t.1)}

/-- A *consumer*: an argument slot of a reachable gate, or an output. -/
abbrev Consumer :=
  Slot p out ⊕ O

variable {p out}

/-- The signal read by a consumer. -/
def consumed : Consumer p out → Signal p out
  | .inl t => ⟨(p.lines t.1.1).wires t.1.2, .arg t.1.2 t.2⟩
  | .inr o => ⟨out o, .output o⟩

variable (p out)

/-- The number of consumers of a signal. -/
noncomputable def fanout (w : Signal p out) : ℕ :=
  Nat.card {c : Consumer p out // consumed c = w}

/-- A *junction*: a copy of a signal for one of its consumers. The junctions of a signal `w`
are numbered `0, ..., fanout w - 1`. -/
abbrev Junction : Type :=
  Σ w : Signal p out, Fin (fanout p out w)

/-! ### The graph -/

/-- The vertices: one per signal, one per junction, and one per output. -/
inductive Vertex
  /-- The vertex of a signal: an input vertex or a gate vertex. -/
  | signal (w : Signal p out)
  /-- A junction. -/
  | junction (j : Junction p out)
  /-- The vertex of an output, which consumes it. -/
  | output (o : O)

/-- The edges: two per junction. -/
inductive Edge : Type
  /-- The edge into a junction from its predecessor in the chain. -/
  | feed (j : Junction p out)
  /-- The edge from a junction to its consumer. -/
  | deliver (j : Junction p out)

variable {p out}

/-- Vertices are signals, junctions, and outputs. -/
def Vertex.equiv : Vertex p out ≃ Signal p out ⊕ Junction p out ⊕ O where
  toFun
    | .signal w => .inl w
    | .junction j => .inr (.inl j)
    | .output o => .inr (.inr o)
  invFun
    | .inl w => .signal w
    | .inr (.inl j) => .junction j
    | .inr (.inr o) => .output o
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with w | j | o <;> rfl

/-- Edges are two copies of the junctions. -/
def Edge.equiv : Edge p out ≃ Junction p out ⊕ Junction p out where
  toFun
    | .feed j => .inl j
    | .deliver j => .inr j
  invFun
    | .inl j => .feed j
    | .inr j => .deliver j
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with j | j <;> rfl

/-- The vertex that consumes through a consumer: a gate vertex or an output vertex. -/
def owner : Consumer p out → Vertex p out
  | .inl t => .signal ⟨.gate t.1.1, t.2⟩
  | .inr o => .output o

/-- The vertex feeding a junction: the signal itself for its first junction, and the previous
junction otherwise. -/
def feeder (j : Junction p out) : Vertex p out :=
  if j.2.val = 0 then .signal j.1
  else .junction ⟨j.1, ⟨j.2.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2.isLt⟩⟩

/-- The source of an edge. -/
def src : Edge p out → Vertex p out
  | .feed j => feeder j
  | .deliver j => .junction j

/-- The signal carried by an edge. -/
def Edge.signal : Edge p out → Signal p out
  | .feed j => j.1
  | .deliver j => j.1

/-- An edge leaving a junction carries the junction's signal. -/
theorem signal_of_src_eq_junction {e : Edge p out} {j : Junction p out}
    (h : src e = .junction j) : e.signal = j.1 := by
  cases e <;> grind [src, feeder, Edge.signal]

/-! ### Delivery

With finitely many outputs every signal has finitely many consumers, and the junctions of a
signal correspond to its consumers. This gives each deliver edge its target. -/

variable [Finite O]

variable (p out) in
/-- Junctions correspond to consumers. -/
noncomputable def junctionEquiv : Junction p out ≃ Consumer p out :=
  (Equiv.sigmaCongrRight fun w =>
      (Finite.equivFin {c : Consumer p out // consumed c = w}).symm).trans
    (Equiv.sigmaFiberEquiv consumed)

/-- The consumer of a junction reads the junction's signal. -/
@[simp] theorem consumed_junctionEquiv (j : Junction p out) :
    consumed (junctionEquiv p out j) = j.1 :=
  ((Finite.equivFin {c : Consumer p out // consumed c = j.1}).symm j.2).2

/-- The junction of a consumer belongs to the consumed signal. -/
@[simp] theorem fst_junctionEquiv_symm (c : Consumer p out) :
    ((junctionEquiv p out).symm c).1 = consumed c := by
  rw [← consumed_junctionEquiv, Equiv.apply_symm_apply]

/-- Every signal has a consumer. -/
theorem fanout_pos (w : Signal p out) : 0 < fanout p out w := by
  obtain ⟨w, o, hw⟩ := w
  refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
  cases hw with
  | refl => exact ⟨⟨.inr o, rfl⟩⟩
  | arg a hg => exact ⟨⟨.inl ⟨⟨_, a⟩, o, hg⟩, rfl⟩⟩

instance : Finite (Vertex p out) := Finite.of_equiv _ Vertex.equiv.symm

instance : Finite (Edge p out) := Finite.of_equiv _ Edge.equiv.symm

/-- The target of an edge. -/
noncomputable def tgt : Edge p out → Vertex p out
  | .feed j => .junction j
  | .deliver j => owner (junctionEquiv p out j)

/-- The edge delivering argument `a` to the reachable gate `g`. -/
noncomputable def argEdge {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) : Edge p out :=
  .deliver ((junctionEquiv p out).symm (.inl ⟨⟨g, a⟩, hg⟩))

/-- The edge delivering an output to its output vertex. -/
noncomputable def outEdge (o : O) : Edge p out :=
  .deliver ((junctionEquiv p out).symm (.inr o))

/-- The first edge of a signal: the feed edge of its first junction. -/
def head (w : Signal p out) : Edge p out :=
  .feed ⟨w, ⟨0, fanout_pos w⟩⟩

@[simp] theorem signal_argEdge {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) :
    (argEdge hg a).signal = ⟨(p.lines g).wires a, .arg a hg⟩ := by
  simp [argEdge, Edge.signal, consumed]

@[simp] theorem signal_outEdge (o : O) : (outEdge o : Edge p out).signal = ⟨out o, .output o⟩ := by
  simp [outEdge, Edge.signal, consumed]

@[simp] theorem tgt_argEdge {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) : tgt (argEdge hg a) = .signal ⟨.gate g, hg⟩ := by
  simp [argEdge, tgt, owner]

@[simp] theorem tgt_outEdge (o : O) : tgt (outEdge o : Edge p out) = .output o := by
  simp [outEdge, tgt, owner]

/-- An edge leaving a signal vertex is the first edge of that signal. -/
theorem eq_head_of_src_eq_signal {e : Edge p out} {w : Signal p out}
    (h : src e = .signal w) : e = head w := by
  cases e <;> grind [src, feeder, head, Fin.ext_iff]

end Proofs.Compiler
