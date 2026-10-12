/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Compiler.Basic
public import Proofs.Network

/-!
# The compiled network and its exactness

Gate, junction, and output constraints accept exactly the program's accepted inputs.
Every satisfying assignment is the program trace on its reachable signals.
-/

@[expose] public section

namespace Proofs.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} {p : Program σ n s} {out : O → Wire n s}

/-! ### The network -/

open Classical in
/-- Each reachable input is read at its signal vertex. -/
noncomputable def site (i : Fin n) : Option (Vertex p out) :=
  if h : Reach p out (.input i) then some (.signal ⟨.input i, h⟩) else none

/-- An input read at a vertex is reachable and read at its signal vertex. -/
theorem site_eq_some {i : Fin n} {v : Vertex p out} (h : site i = some v) :
    ∃ hi : Reach p out (.input i), v = .signal ⟨.input i, hi⟩ := by
  grind [site]

/-- A reachable input is read at its signal vertex. -/
theorem site_of_reach {i : Fin n} (hi : Reach p out (.input i)) :
    site i = some (.signal ⟨.input i, hi⟩ : Vertex p out) := by
  simp [site, hi]

variable [Finite O] {U : Type*} (I : Interpretation σ U) (Acc : O → Set U)

/-- The value a signal vertex puts on its outgoing edge: the input itself for an input wire,
and the gate's operation applied to its incoming argument edges for a gate wire. -/
noncomputable def emit : (w : Wire n s) → Reach p out w → (Fin n → U) → (Edge p out → U) → U
  | .input i, _, x, _ => x i
  | .gate g, hg, _, α => I (p.lines g).op fun a => α (argEdge hg a)

/-- The constraint at each vertex. -/
noncomputable def check : Vertex p out → (Fin n → U) → (Edge p out → U) → Prop
  | .signal w, x, α => ∀ e, src e = .signal w → α e = emit I w.1 w.2 x α
  | .junction j, _, α => ∀ e, src e = .junction j → α e = α (.feed j)
  | .output o, _, α => α (outEdge o) ∈ Acc o

variable (p out)

/-- **The constraint network of a program** with outputs `out`, accepting at the output `o` the
values in `Acc o`. -/
noncomputable def network : Network U (Fin n) (Vertex p out) (Edge p out) where
  src := src
  tgt := tgt
  site := site
  Check := check I Acc
  check_local v x x' α α' hx hα hc := by
    cases v with
    | signal w =>
      obtain ⟨w, hw⟩ := w
      intro e he
      rw [← hα e (Or.inl he), hc e he]
      cases w with
      | input i => exact hx i (site_of_reach hw)
      | gate g =>
        simp only [emit]
        congr 1
        funext a
        exact hα _ (Or.inr (tgt_argEdge hw a))
    | junction j =>
      intro e he
      rw [← hα e (Or.inl he), hc e he]
      exact hα _ (Or.inr rfl)
    | output o =>
      change α' (outEdge o) ∈ Acc o
      rw [← hα _ (Or.inr (tgt_outEdge o))]
      exact hc

variable {p out}

/-! ### Exactness -/

/-- The run of the program puts the value of each signal on each of its edges. -/
theorem trace_satisfies {x : Fin n → U} (hx : ∀ o, p.trace I x (out o) ∈ Acc o) :
    (network p out I Acc).Satisfies x fun e => p.trace I x e.signal.1 := by
  intro v
  cases v with
  | signal w =>
    obtain ⟨w, hw⟩ := w
    intro e he
    rw [eq_head_of_src_eq_signal he]
    cases w with
    | input i => rfl
    | gate g =>
      simp only [head, Edge.signal, emit]
      exact p.trace_gate I x g
  | junction j =>
    intro e he
    change p.trace I x e.signal.1 = p.trace I x j.1.1
    rw [signal_of_src_eq_junction he]
  | output o =>
    change p.trace I x (outEdge o).signal.1 ∈ Acc o
    simpa using hx o

section Satisfying

variable {I Acc} {x : Fin n → U} {α : Edge p out → U}
  (hα : (network p out I Acc).Satisfies x α)
include hα

/-- In a satisfying assignment, the feed edges along the junction chain of a signal all carry
the value of its first edge. -/
theorem feed_eq_head (w : Signal p out) :
    ∀ (k : ℕ) (hk : k < fanout p out w), α (.feed ⟨w, ⟨k, hk⟩⟩) = α (head w)
  | 0, _ => rfl
  | k + 1, hk => by
    have hprev : src (.feed ⟨w, ⟨k + 1, hk⟩⟩ : Edge p out) = .junction ⟨w, ⟨k, by lia⟩⟩ := by
      simp [src, feeder]
    rw [hα (.junction _) _ hprev]
    exact feed_eq_head w k _

/-- In a satisfying assignment, every edge carries the value of the first edge of its
signal. -/
theorem eq_head (e : Edge p out) : α e = α (head e.signal) := by
  rcases e with ⟨w, k⟩ | ⟨w, k⟩
  · exact feed_eq_head hα w k k.isLt
  · rw [hα (.junction ⟨w, k⟩) (.deliver ⟨w, k⟩) rfl]
    exact feed_eq_head hα w k k.isLt

/-- In a satisfying assignment, every signal carries its value in the run of the program. -/
theorem head_eq_trace : ∀ (w : Wire n s) (hw : Reach p out w), α (head ⟨w, hw⟩) = p.trace I x w
  | .input i, hw => hα (.signal ⟨.input i, hw⟩) _ rfl
  | .gate g, hw => by
    rw [hα (.signal ⟨.gate g, hw⟩) _ rfl, p.trace_gate I x g]
    simp only [emit]
    congr 1
    funext a
    rw [eq_head hα, signal_argEdge]
    exact head_eq_trace _ _
termination_by w => match w with | .input _ => 0 | .gate g => g.val + 1
decreasing_by
  generalize hw' : (p.lines g).wires a = w' at *
  cases w' with
  | input => simp
  | gate g' => simpa using p.lines_wires_eq_gate_lt g a hw'

/-- **Uniqueness.** A satisfying assignment puts on every edge the value of its signal in the
run of the program. -/
theorem eq_trace (e : Edge p out) : α e = p.trace I x e.signal.1 := by
  rw [eq_head hα, head_eq_trace hα]

end Satisfying

/-- **Exactness.** The network accepts exactly the inputs on which every output `o` lies in
`Acc o`. -/
theorem accepted_network :
    (network p out I Acc).accepted = {x | ∀ o, p.trace I x (out o) ∈ Acc o} := by
  ext x
  constructor
  · rintro ⟨α, hα⟩ o
    have hacc : α (outEdge o) ∈ Acc o := hα (.output o)
    rwa [eq_trace hα, signal_outEdge] at hacc
  · exact fun hx => ⟨_, trace_satisfies I Acc hx⟩

variable {I Acc} in
/-- Every input has at most one satisfying assignment: the run of the program. -/
theorem satisfies_unique {x : Fin n → U} {α β : Edge p out → U}
    (hα : (network p out I Acc).Satisfies x α) (hβ : (network p out I Acc).Satisfies x β) :
    α = β :=
  funext fun e => (eq_trace hα e).trans (eq_trace hβ e).symm

/-- **Unambiguity.** Along any layout, the read-once branching program of the network has at
most one accepting path per input, since every satisfying assignment is the run of the
program. -/
theorem unambiguous_branchingProgram (π : Layout (Vertex p out)) :
    ((network p out I Acc).branchingProgram π).Unambiguous :=
  Network.unambiguous_branchingProgram _ π fun _ _ _ => satisfies_unique

end Proofs.Compiler
