/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Compiler.Network

/-!
# Degrees and connectivity of the compiler graph

For a fan-in bound `r ≥ 2`, the graph has maximum degree at most `r + 1`. It is connected when
one wire is upstream of every output; single-output circuits satisfy this last condition.
-/

@[expose] public section

namespace Proofs.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} {p : Program σ n s} {out : O → Wire n s}

/-! ### Degrees -/

/-- A gate has at most `r` slots when the fan-in is at most `r`. -/
theorem ncard_slots_le {r : ℕ} (hfan : p.FanInAtMost r) (w : Wire n s) :
    {t : Slot p out | Wire.gate t.1.1 = w}.ncard ≤ r := by
  calc {t : Slot p out | Wire.gate t.1.1 = w}.ncard
      ≤ ((Finset.range r : Finset ℕ) : Set ℕ).ncard := by
        refine ncard_le_ncard_of_injOn (fun t => t.1.2.val) ?_ ?_ (toFinite _)
        · intro t _
          simpa using t.1.2.isLt.trans_le (hfan.arity_le t.1.1)
        · rintro ⟨⟨g, a⟩, hg⟩ hw ⟨⟨g', a'⟩, hg'⟩ hw' haa'
          simp only [mem_ofPred_eq] at hw hw'
          obtain rfl : g = g' := Wire.gate.inj (hw.trans hw'.symm)
          obtain rfl : a = a' := Fin.ext haa'
          rfl
    _ = r := by rw [ncard_coe_finset, Finset.card_range]

/-- Two junctions fed by the same junction are equal. -/
theorem eq_of_feeder_eq_junction {j₁ j₂ j : Junction p out} (h₁ : feeder j₁ = .junction j)
    (h₂ : feeder j₂ = .junction j) : j₁ = j₂ := by
  rcases j₁ with ⟨w₁, k₁⟩
  rcases j₂ with ⟨w₂, k₂⟩
  grind [feeder, Sigma.ext_iff, Fin.ext_iff]

variable [Finite O] {U : Type*} (I : Interpretation σ U) (Acc : O → Set U)

/-- The edge delivering a slot's signal to its gate. -/
noncomputable def slotEdge (t : Slot p out) : Edge p out :=
  .deliver ((junctionEquiv p out).symm (.inl t))

/-- An edge entering a signal vertex delivers one of the slots of its gate. -/
theorem exists_slot_of_tgt_eq_signal {e : Edge p out} {w : Signal p out}
    (h : tgt e = .signal w) : ∃ t : Slot p out, Wire.gate t.1.1 = w.1 ∧ e = slotEdge t := by
  rcases e with j | j
  · cases h
  · simp only [tgt] at h
    rcases hj : junctionEquiv p out j with t | o <;> rw [hj] at h
    · simp only [owner, Vertex.signal.injEq] at h
      exact ⟨t, congrArg Subtype.val h, by simp [slotEdge, ← hj]⟩
    · cases h

/-- **The degrees are bounded.** When the gates have fan-in at most `r ≥ 2`, every vertex has
degree at most `r + 1`: a gate vertex has its argument edges and one outgoing edge, a junction
has three edges, and input vertices and output vertices have one. For fan-in two the graph is
subcubic. -/
theorem maxDegreeLE {r : ℕ} (hr : 2 ≤ r) (hfan : p.FanInAtMost r) :
    (network p out I Acc).MaxDegreeLE (r + 1) := by
  intro v
  cases v with
  | signal w =>
    -- The first edge of the signal, and the edges delivering the slots of its gate.
    calc ((network p out I Acc).edgesAt (.signal w)).ncard
        ≤ (insert (head w) (slotEdge '' {t : Slot p out | Wire.gate t.1.1 = w.1})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · exact Or.inl (eq_head_of_src_eq_signal he)
          · obtain ⟨t, ht, rfl⟩ := exists_slot_of_tgt_eq_signal he
            exact Or.inr ⟨t, ht, rfl⟩
      _ ≤ (slotEdge '' {t : Slot p out | Wire.gate t.1.1 = w.1}).ncard + 1 := ncard_insert_le _ _
      _ ≤ {t : Slot p out | Wire.gate t.1.1 = w.1}.ncard + 1 := by
          gcongr; exact ncard_image_le (toFinite _)
      _ ≤ r + 1 := by have := ncard_slots_le (out := out) hfan w.1; lia
  | junction j =>
    -- Its feed and deliver edges, and the feed edge of the next junction.
    calc ((network p out I Acc).edgesAt (.junction j)).ncard
        ≤ (insert (Edge.feed j) (insert (Edge.deliver j)
            {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with j' | j'
            · exact Or.inr (Or.inr ⟨j', he, rfl⟩)
            · cases he; exact Or.inr (Or.inl rfl)
          · rcases e with j' | j'
            · cases he; exact Or.inl rfl
            · simp only [network, tgt] at he
              rcases hj : junctionEquiv p out j' with t | o <;> rw [hj] at he <;> cases he
      _ ≤ {e | ∃ j', feeder j' = .junction j ∧ e = (.feed j' : Edge p out)}.ncard + 1 + 1 :=
          (ncard_insert_le _ _).trans (by gcongr; exact ncard_insert_le _ _)
      _ ≤ r + 1 := by
          have : {e | ∃ j', feeder j' = .junction j ∧ e = (.feed j' : Edge p out)}.ncard ≤ 1 :=
            (ncard_le_one (toFinite _)).mpr fun _ ⟨j₁, h₁, he₁⟩ _ ⟨j₂, h₂, he₂⟩ =>
              he₁.trans ((eq_of_feeder_eq_junction h₁ h₂) ▸ he₂.symm)
          lia
  | output o =>
    -- Only the edge delivering the output.
    calc ((network p out I Acc).edgesAt (.output o)).ncard
        ≤ ({outEdge o} : Set (Edge p out)).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with j | j
            · simp only [network, src, feeder] at he; split_ifs at he
            · cases he
          · rcases e with j | j
            · cases he
            · simp only [network, tgt] at he
              rcases hj : junctionEquiv p out j with t | o' <;> rw [hj] at he
              · cases he
              · cases he; simp [outEdge, ← hj]
      _ ≤ r + 1 := by simp

/-! ### Connectivity -/

/-- Every junction of a signal is joined to the signal along its chain. -/
theorem reflTransGen_junction_signal (w : Signal p out) :
    ∀ (k : ℕ) (hk : k < fanout p out w),
      Relation.ReflTransGen (network p out I Acc).Adj (.junction ⟨w, ⟨k, hk⟩⟩) (.signal w)
  | 0, _ => .single ⟨.feed ⟨w, ⟨0, _⟩⟩, Or.inr ⟨by simp [network, src, feeder], rfl⟩⟩
  | k + 1, hk => .head ⟨.feed ⟨w, ⟨k + 1, hk⟩⟩, Or.inr ⟨by simp [network, src, feeder], rfl⟩⟩
      (reflTransGen_junction_signal w k (by lia))

/-- Every junction is joined to its signal. -/
theorem reflTransGen_junction (j : Junction p out) :
    Relation.ReflTransGen (network p out I Acc).Adj (.junction j) (.signal j.1) :=
  reflTransGen_junction_signal I Acc j.1 j.2.val j.2.isLt

/-- Each output signal is joined to its output vertex. -/
theorem reflTransGen_out (o : O) :
    Relation.ReflTransGen (network p out I Acc).Adj (.signal ⟨out o, .output o⟩) (.output o) := by
  have hj := reflTransGen_junction I Acc ((junctionEquiv p out).symm (.inr o))
  rw [fst_junctionEquiv_symm] at hj
  exact (Multigraph.reflTransGen_adj_symm hj).tail ⟨outEdge o, Or.inl ⟨rfl, tgt_outEdge o⟩⟩

/-- Each argument of a reachable gate is joined to the gate, along its chain. -/
theorem reflTransGen_arg {g : Fin s} (hg : Reach p out (.gate g))
    (a : Fin (σ.Arity (p.lines g).op)) :
    Relation.ReflTransGen (network p out I Acc).Adj (.signal ⟨_, .arg a hg⟩)
      (.signal ⟨.gate g, hg⟩) := by
  have hj := reflTransGen_junction I Acc ((junctionEquiv p out).symm (.inl ⟨⟨g, a⟩, hg⟩))
  rw [fst_junctionEquiv_symm] at hj
  exact (Multigraph.reflTransGen_adj_symm hj).tail ⟨argEdge hg a, Or.inl ⟨rfl, tgt_argEdge hg a⟩⟩

/-- A wire upstream of an output is joined to the output vertex. -/
theorem reflTransGen_of_upstream {o : O} {w : Wire n s} (h : p.Upstream (out o) w) :
    Relation.ReflTransGen (network p out I Acc).Adj (.signal ⟨w, o, h⟩) (.output o) := by
  induction h with
  | refl => exact reflTransGen_out I Acc o
  | @arg g a hg ih => exact (reflTransGen_arg I Acc ⟨o, hg⟩ a).trans ih

/-- **The graph is connected** when some wire is upstream of every output. -/
theorem connected_of_upstream {w₀ : Wire n s} (h₀ : ∀ o, p.Upstream (out o) w₀) :
    (network p out I Acc).Connected := by
  -- Every vertex is joined to some output vertex, and every output vertex to `w₀`.
  have hout : ∀ v : Vertex p out, ∃ o, Relation.ReflTransGen (network p out I Acc).Adj v
      (.output o) := by
    intro v
    cases v with
    | signal w =>
      obtain ⟨o, ho⟩ := w.2
      exact ⟨o, reflTransGen_of_upstream I Acc ho⟩
    | junction j =>
      obtain ⟨o, ho⟩ := j.1.2
      exact ⟨o, (reflTransGen_junction I Acc j).trans (reflTransGen_of_upstream I Acc ho)⟩
    | output o => exact ⟨o, .refl⟩
  intro u v
  obtain ⟨o, hu⟩ := hout u
  obtain ⟨o', hv⟩ := hout v
  exact (hu.trans (Multigraph.reflTransGen_adj_symm (reflTransGen_of_upstream I Acc (h₀ o)))).trans
    ((reflTransGen_of_upstream I Acc (h₀ o')).trans (Multigraph.reflTransGen_adj_symm hv))

/-- **The graph of a circuit with at most one output is connected.** -/
theorem connected [Subsingleton O] : (network p out I Acc).Connected := by
  rcases isEmpty_or_nonempty O with hO | ⟨⟨o₀⟩⟩
  · intro u v
    cases u with
    | signal w =>
      obtain ⟨o, -⟩ := w.2
      exact isEmptyElim o
    | junction j =>
      obtain ⟨o, -⟩ := j.1.2
      exact isEmptyElim o
    | output o => exact isEmptyElim o
  · exact connected_of_upstream I Acc (w₀ := out o₀) fun o => Subsingleton.elim o₀ o ▸ .refl

end Proofs.Compiler
