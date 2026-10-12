/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Support
public import Proofs.Layouts.Scores
import Mathlib.Tactic.Linarith

/-!
# Ordering multigraph vertices by scores

Sort the vertices of a multigraph by a real score. The cuts below a grid of thresholds and the
numbers of vertices in the windows between them bound the cut of every prefix, counting
parallel edges separately.
-/

@[expose] public section

namespace Proofs.Multigraph

open Finset

variable {W E : Type} [Fintype W] [Fintype E] (G : Multigraph W E)

omit [Fintype W] in
theorem mem_cutFinset_iff {P : Finset W} {e : E} : e ∈ G.cutFinset P ↔
    ∃ u v, ((G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u)) ∧
      u ∈ P ∧ v ∉ P := by
  rw [mem_cutFinset]
  grind

/-- **Grid control.** Let `P` be a threshold set of `score` at `m`. If `d` times the number of
vertices in each tail, and the cut below each grid threshold plus `d` times the number of
vertices in the following window, are at most `B`, then at most `B` edges leave `P`. -/
theorem card_cut_le_grid {d : ℕ} (degree : G.MaxDegreeLE d) (score : W → ℝ)
    (P : Finset W) {m a δ : ℝ} (hP : ∀ v ∈ P, score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ score v) (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + M * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((G.cutFinset {v | score v < a + i * δ}).card : ℝ) +
        d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ((G.cutFinset P).card : ℝ) ≤ B := by
  classical
  have count (S : Finset W)
      (hsub : G.cutFinset P ⊆ (G.touching (S : Set W)).toFinset) :
      ((G.cutFinset P).card : ℝ) ≤ d * S.card := by
    have hb : (G.touching (S : Set W)).toFinset.card ≤ d * S.card := by
      rw [← Set.ncard_eq_toFinset_card']; exact G.ncard_touching_le degree S
    have h := (card_le_card hsub).trans hb
    exact_mod_cast h
  have touch {e : E} {u v : W} {S : Finset W}
      (hedge : (G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u))
      (hu : u ∈ S) : e ∈ (G.touching (S : Set W)).toFinset := by
    rw [Set.mem_toFinset]
    rcases hedge with ⟨hs, _⟩ | ⟨_, ht⟩
    · exact Or.inl (hs ▸ hu)
    · exact Or.inr (ht ▸ hu)
  by_cases hlo : m < a
  · refine (count {v | score v < a} ?_).trans low
    intro e he
    obtain ⟨u, v, hedge, hu, _⟩ := G.mem_cutFinset_iff.mp he
    exact touch hedge (mem_filter.mpr ⟨mem_univ _, (hP u hu).trans_lt hlo⟩)
  by_cases hhi : a + M * δ ≤ m
  · refine (count {v | a + M * δ ≤ score v} ?_).trans high
    intro e he
    obtain ⟨u, v, hedge, _, hv⟩ := G.mem_cutFinset_iff.mp he
    exact touch (u := v) (v := u) (hedge.elim Or.inr Or.inl)
      (mem_filter.mpr ⟨mem_univ _, hhi.trans (hPc v hv)⟩)
  obtain ⟨i, hi, ht, ht'⟩ := exists_grid_index hδ (M := M) (not_lt.mp hlo) (not_le.mp hhi)
  let window : Finset W := {v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ}
  have hsub : G.cutFinset P ⊆ G.cutFinset {v | score v < a + i * δ} ∪
      (G.touching (window : Set W)).toFinset := by
    intro e he
    obtain ⟨u, v, hedge, hu, hv⟩ := G.mem_cutFinset_iff.mp he
    rw [mem_union]
    by_cases hut : score u < a + i * δ
    · left
      exact G.mem_cutFinset_iff.mpr ⟨u, v, hedge,
        mem_filter.mpr ⟨mem_univ _, hut⟩,
        fun h => not_lt_of_ge (ht.trans (hPc v hv)) (mem_filter.mp h).2⟩
    · right
      exact touch hedge (mem_filter.mpr ⟨mem_univ _, le_of_not_gt hut,
        (hP u hu).trans_lt ht'⟩)
  have hwindow : (G.touching (window : Set W)).toFinset.card ≤ d * window.card := by
    rw [← Set.ncard_eq_toFinset_card']; exact G.ncard_touching_le degree window
  have hnat := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left hwindow _))
  have hreal : ((G.cutFinset P).card : ℝ) ≤
      (G.cutFinset {v | score v < a + i * δ}).card + d * window.card := by exact_mod_cast hnat
  exact hreal.trans (by simpa only [window, Nat.cast_add, Nat.cast_one] using mid i hi)

/-- **Sorting by a score.** Under the grid hypotheses of `card_cut_le_grid`, the vertices have
an injective key all of whose prefixes are crossed by at most `B` edges. -/
theorem exists_key_of_vertexScore {d : ℕ} (degree : G.MaxDegreeLE d) (score : W → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + M * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((G.cutFinset {v | score v < a + i * δ}).card : ℝ) +
        d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
      ((G.cutFinset {v | key v < t}).card : ℝ) ≤ B := by
  obtain ⟨key, hinj, hkey⟩ := exists_key_of_score score
  refine ⟨key, hinj, fun t => ?_⟩
  rcases hkey t with hempty | ⟨m, hP, hPc⟩
  · have hB : 0 ≤ B := le_trans (by positivity) low
    have : ({v | key v < t} : Finset W) = ∅ := filter_eq_empty_iff.mpr fun v _ => hempty v
    simpa [this, cutFinset] using hB
  · exact G.card_cut_le_grid degree score _ (fun v hv => hP v (mem_filter.mp hv).2)
      (fun v hv => hPc v fun h => hv (mem_filter.mpr ⟨mem_univ _, h⟩)) hδ M low high mid

end Proofs.Multigraph
