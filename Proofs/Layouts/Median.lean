/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Cubic
public import Proofs.Layouts.Scores
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

/-!
# Ordering a cubic graph by median edge scores

Give every edge of a cubic graph a real *score*. Each vertex has three incident edges, hence a
*median* score, and we list the vertices by their medians. This file bounds the cut of every
prefix of that list in terms of how the scores fall around a grid of thresholds
`a, a + δ, ..., a + M δ`. A vertex *straddles* a threshold `t` when one of its edges scores
below `t` and another at least `t`.

**The cut of a prefix** (`card_cutFinset_le`). Let `P` be a set of vertices whose medians are
all at most some `m`, while the medians outside `P` are all at least `m`. An edge leaving `P`
that scores below a threshold `t ≤ m` is charged to its endpoint outside `P`: that endpoint
has its median above the edge's score, so it is charged at most once. An edge scoring at least
a threshold `t' > m` is charged to its endpoint inside `P`, again at most once. If
`a + i δ ≤ m < a + (i + 1) δ`, every vertex charged in this way straddles `a + i δ` or is an
endpoint of an edge scoring in the window `[a + i δ, a + (i + 1) δ)`, so the cut has at most

`#(vertices straddling a + i δ) + 3 #(edges scoring in the window)`

edges. If `m` lies below the grid, or above it, the cut is at most three times the number of
edges in the lower, or upper, tail.

**The layout** (`exists_key_of_edgeScore`). Listing the vertices by median, with ties broken
arbitrarily, every prefix has the property above, so all prefix cuts are bounded at once.
-/

@[expose] public section

namespace Proofs

open Finset

variable {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The vertex `v` *straddles* the threshold `t`: an edge at `v` scores below `t` and another
scores at least `t`. -/
def EdgeStraddles (score : Sym2 W → ℝ) (t : ℝ) (v : W) : Prop :=
  ∃ e ∈ H.incidenceFinset v, score e < t ∧ ∃ e' ∈ H.incidenceFinset v, t ≤ score e'

noncomputable instance (score : Sym2 W → ℝ) (t : ℝ) : DecidablePred (EdgeStraddles H score t) :=
  fun _ => by unfold EdgeStraddles; infer_instance

/-- `m` is a *median* of the edge scores at `v`: at least two edges at `v` score at most `m`,
and at least two score at least `m`. -/
def IsMedian (score : Sym2 W → ℝ) (v : W) (m : ℝ) : Prop :=
  2 ≤ #{e ∈ H.incidenceFinset v | score e ≤ m} ∧ 2 ≤ #{e ∈ H.incidenceFinset v | m ≤ score e}

variable {H}

theorem card_incidenceFinset_of_regular (regular : H.IsRegularOfDegree 3) (v : W) :
    #(H.incidenceFinset v) = 3 := by
  rw [SimpleGraph.card_incidenceFinset_eq_degree, regular.degree_eq]

/-- Every vertex of a cubic graph has a median edge score. -/
theorem exists_isMedian (regular : H.IsRegularOfDegree 3) (score : Sym2 W → ℝ) (v : W) :
    ∃ m, IsMedian H score v m := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ :=
    card_eq_three.mp (card_incidenceFinset_of_regular regular v)
  rcases le_total (score a) (score b) with h | h <;>
    rcases le_total (score a) (score c) with h' | h' <;>
    rcases le_total (score b) (score c) with h'' | h'' <;>
    solve
      | refine ⟨score a, ?_⟩
        simp_all [IsMedian, filter_insert, filter_singleton]; split_ifs <;> simp_all
      | refine ⟨score b, ?_⟩
        simp_all [IsMedian, filter_insert, filter_singleton]; split_ifs <;> simp_all
      | refine ⟨score c, ?_⟩
        simp_all [IsMedian, filter_insert, filter_singleton]; split_ifs <;> simp_all

/-- At most one edge at a vertex scores above a median. -/
theorem IsMedian.card_lt_le_one (regular : H.IsRegularOfDegree 3) {score : Sym2 W → ℝ}
    {v : W} {m : ℝ} (h : IsMedian H score v m) :
    #{e ∈ H.incidenceFinset v | m < score e} ≤ 1 := by
  have := card_filter_add_card_filter_not (s := H.incidenceFinset v) (fun e => score e ≤ m)
  simp only [not_le, card_incidenceFinset_of_regular regular] at this
  grind [IsMedian]

/-- At most one edge at a vertex scores below a median. -/
theorem IsMedian.card_gt_le_one (regular : H.IsRegularOfDegree 3) {score : Sym2 W → ℝ}
    {v : W} {m : ℝ} (h : IsMedian H score v m) :
    #{e ∈ H.incidenceFinset v | score e < m} ≤ 1 := by
  have := card_filter_add_card_filter_not (s := H.incidenceFinset v) (fun e => m ≤ score e)
  simp only [not_le, card_incidenceFinset_of_regular regular] at this
  grind [IsMedian]

omit [Fintype W] in
/-- Edges each with an endpoint in `Q`, no two sharing such an endpoint, number at most `|Q|`. -/
theorem card_le_of_endpoints {C : Finset (Sym2 W)} {Q : Finset W}
    (hend : ∀ e ∈ C, ∃ v ∈ Q, v ∈ e)
    (huniq : ∀ v ∈ Q, ∀ e ∈ C, ∀ e' ∈ C, v ∈ e → v ∈ e' → e = e') : #C ≤ #Q := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp
  have : Nonempty W := ⟨(hend e₀ he₀).choose⟩
  choose! g hgQ hge using hend
  exact card_le_card_of_injOn g (fun e he => hgQ e he) fun e he e' he' h =>
    huniq (g e) (hgQ e he) e he e' he' (hge e he) (h ▸ hge e' he')

/-- The endpoints of a set of edges number at most twice the edges. -/
theorem card_endpoints_le [DecidableEq W] (D : Finset (Sym2 W)) :
    #{w | ∃ e ∈ D, w ∈ e} ≤ 2 * #D := by
  calc _ = #(D.biUnion fun e => e.toFinset) := by
        congr 1; ext w; simp
    _ ≤ ∑ e ∈ D, #e.toFinset := card_biUnion_le
    _ ≤ ∑ _e ∈ D, 2 := sum_le_sum fun e _ => by
        simp only [Sym2.card_toFinset]; split_ifs <;> norm_num
    _ = 2 * #D := by simp [Nat.mul_comm]

/-! ### The cut of a prefix -/

section Cut

variable {score : Sym2 W → ℝ} {med : W → ℝ} {P : Finset W} {m : ℝ}

/-- An edge leaving `P` is incident to its endpoints. -/
private theorem exists_endpoints {e : Sym2 W} (he : e ∈ H.cutFinset P) :
    ∃ u v, e ∈ H.incidenceFinset u ∧ e ∈ H.incidenceFinset v ∧ u ∈ P ∧ v ∉ P := by
  obtain ⟨hedge, a, b, rfl, ha, hb⟩ := SimpleGraph.mem_cutFinset.mp he
  refine ⟨a, b, ?_, ?_, ha, hb⟩ <;>
    exact SimpleGraph.mem_incidenceFinset.mpr ⟨hedge, by simp⟩

/-- Edges leaving `P` that score below a threshold `t ≤ m` are no more than the vertices
outside `P` with an edge scoring below `t`. -/
theorem card_cut_lt_le [DecidableEq W] (regular : H.IsRegularOfDegree 3)
    (hmed : ∀ v, IsMedian H score v (med v))
    (hPc : ∀ v ∉ P, m ≤ med v) {t : ℝ} (ht : t ≤ m) :
    #{e ∈ H.cutFinset P | score e < t} ≤
      #{v | v ∉ P ∧ ∃ e ∈ H.incidenceFinset v, score e < t} := by
  refine card_le_of_endpoints (fun e he => ?_) fun v hv e he e' he' hve hve' => ?_
  · obtain ⟨he, hlt⟩ := mem_filter.mp he
    obtain ⟨_, v, _, hev, _, hv⟩ := exists_endpoints he
    exact ⟨v, mem_filter.mpr ⟨mem_univ _, hv, e, hev, hlt⟩, (SimpleGraph.mem_incidenceFinset.mp
      hev).2⟩
  · -- Both edges score below the median of `v`, and at most one edge at `v` does.
    obtain ⟨hv, -⟩ := (mem_filter.mp hv).2
    have hmv := (hPc v hv)
    have hin : ∀ f ∈ ({e ∈ H.cutFinset P | score e < t} : Finset _), v ∈ f →
        f ∈ ({f ∈ H.incidenceFinset v | score f < med v} : Finset _) := by
      simp only [mem_filter, SimpleGraph.mem_incidenceFinset]
      grind [SimpleGraph.mem_cutFinset, SimpleGraph.incidenceSet]
    exact card_le_one.mp ((hmed v).card_gt_le_one regular) e (hin e he hve) e' (hin e' he' hve')

/-- Edges leaving `P` that score at least a threshold `t > m` are no more than the vertices
inside `P` with an edge scoring at least `t`. -/
theorem card_cut_ge_le [DecidableEq W] (regular : H.IsRegularOfDegree 3)
    (hmed : ∀ v, IsMedian H score v (med v))
    (hP : ∀ u ∈ P, med u ≤ m) {t : ℝ} (ht : m < t) :
    #{e ∈ H.cutFinset P | t ≤ score e} ≤
      #{u | u ∈ P ∧ ∃ e ∈ H.incidenceFinset u, t ≤ score e} := by
  refine card_le_of_endpoints (fun e he => ?_) fun u hu e he e' he' hue hue' => ?_
  · obtain ⟨he, hge⟩ := mem_filter.mp he
    obtain ⟨u, _, heu, _, hu, _⟩ := exists_endpoints he
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, hu, e, heu, hge⟩, (SimpleGraph.mem_incidenceFinset.mp
      heu).2⟩
  · -- Both edges score above the median of `u`, and at most one edge at `u` does.
    obtain ⟨hu, -⟩ := (mem_filter.mp hu).2
    have hmu := hP u hu
    have hin : ∀ f ∈ ({e ∈ H.cutFinset P | t ≤ score e} : Finset _), u ∈ f →
        f ∈ ({f ∈ H.incidenceFinset u | med u < score f} : Finset _) := by
      simp only [mem_filter, SimpleGraph.mem_incidenceFinset]
      grind [SimpleGraph.mem_cutFinset, SimpleGraph.incidenceSet]
    exact card_le_one.mp ((hmed u).card_lt_le_one regular) e (hin e he hue) e' (hin e' he' hue')

/-- A vertex has an edge scoring at most its median. -/
private theorem exists_le_med (hmed : ∀ v, IsMedian H score v (med v)) (v : W) :
    ∃ e ∈ H.incidenceFinset v, score e ≤ med v := by
  simpa only [filter_nonempty_iff] using card_pos.mp (lt_of_lt_of_le two_pos (hmed v).1)

/-- A vertex has an edge scoring at least its median. -/
private theorem exists_ge_med (hmed : ∀ v, IsMedian H score v (med v)) (v : W) :
    ∃ e ∈ H.incidenceFinset v, med v ≤ score e := by
  simpa only [filter_nonempty_iff] using card_pos.mp (lt_of_lt_of_le two_pos (hmed v).2)

/-- **The cut of a prefix.** Let `P` have all medians at most `m` and all medians outside it at
least `m`. If the edges in each tail, and the straddling vertices and window edges at every
grid threshold, are few, then few edges leave `P`. -/
theorem card_cutFinset_le (regular : H.IsRegularOfDegree 3)
    (hmed : ∀ v, IsMedian H score v (med v)) (hP : ∀ u ∈ P, med u ≤ m)
    (hPc : ∀ v ∉ P, m ≤ med v) {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 3 * (#{e ∈ H.edgeFinset | score e < a} : ℝ) ≤ B)
    (high : 3 * (#{e ∈ H.edgeFinset | a + M * δ ≤ score e} : ℝ) ≤ B)
    (mid : ∀ i < M, (#{v | EdgeStraddles H score (a + i * δ) v} : ℝ) +
      3 * (#{e ∈ H.edgeFinset | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ} : ℝ) ≤ B) :
    (#(H.cutFinset P) : ℝ) ≤ B := by
  classical
  have hcut : H.cutFinset P ⊆ H.edgeFinset := SimpleGraph.cutFinset_subset_edgeFinset P
  -- Split the cut at two thresholds `t ≤ t'`.
  have hsplit : ∀ {t t' : ℝ}, t ≤ t' → #(H.cutFinset P) ≤
      #{e ∈ H.cutFinset P | score e < t} +
        #{e ∈ H.cutFinset P | t ≤ score e ∧ score e < t'} +
        #{e ∈ H.cutFinset P | t' ≤ score e} := by
    intro t t' htt'
    calc #(H.cutFinset P)
        ≤ #({e ∈ H.cutFinset P | score e < t} ∪
            {e ∈ H.cutFinset P | t ≤ score e ∧ score e < t'} ∪
            {e ∈ H.cutFinset P | t' ≤ score e}) := by
          refine card_le_card fun e he => ?_
          simp only [mem_union, mem_filter]
          grind
      _ ≤ _ := (card_union_le _ _).trans (add_le_add (card_union_le _ _) le_rfl)
  -- The edges of a filtered cut lie among the edges of the graph.
  have hsub : ∀ p : Sym2 W → Prop, [DecidablePred p] →
      #{e ∈ H.cutFinset P | p e} ≤ #{e ∈ H.edgeFinset | p e} :=
    fun p _ => card_le_card (filter_subset_filter _ hcut)
  set top := a + M * δ
  rcases lt_or_ge m a with hlow | hge
  · -- Below the grid: every vertex of `P` charged by an upper edge is an endpoint of a low edge.
    have hU : #{u | u ∈ P ∧ ∃ e ∈ H.incidenceFinset u, a ≤ score e} ≤
        #{w | ∃ e ∈ ({e ∈ H.edgeFinset | score e < a} : Finset _), w ∈ e} := by
      refine card_le_card fun u hu => ?_
      obtain ⟨hu, -⟩ := (mem_filter.mp hu).2
      obtain ⟨e, he, hle⟩ := exists_le_med hmed u
      have he' := SimpleGraph.mem_incidenceFinset.mp he
      exact mem_filter.mpr ⟨mem_univ _, e, mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr he'.1,
        by linarith [hP u hu]⟩, he'.2⟩
    have hsplit' := hsplit (le_refl a)
    have hge := card_cut_ge_le regular hmed hP hlow
    have hend := card_endpoints_le ({e ∈ H.edgeFinset | score e < a} : Finset _)
    have hlow' := hsub (fun e => score e < a)
    have hmid : #{e ∈ H.cutFinset P | a ≤ score e ∧ score e < a} = 0 := by
      simp
    have hnat : #(H.cutFinset P) ≤ 3 * #{e ∈ H.edgeFinset | score e < a} := by lia
    exact (by exact_mod_cast hnat : (#(H.cutFinset P) : ℝ) ≤ _).trans low
  rcases le_or_gt top m with htop | hlt
  · -- Above the grid: every vertex outside `P` charged by a lower edge is an endpoint of a high
    -- edge.
    have hV : #{v | v ∉ P ∧ ∃ e ∈ H.incidenceFinset v, score e < top} ≤
        #{w | ∃ e ∈ ({e ∈ H.edgeFinset | top ≤ score e} : Finset _), w ∈ e} := by
      refine card_le_card fun v hv => ?_
      obtain ⟨hv, -⟩ := (mem_filter.mp hv).2
      obtain ⟨e, he, hge⟩ := exists_ge_med hmed v
      have he' := SimpleGraph.mem_incidenceFinset.mp he
      exact mem_filter.mpr ⟨mem_univ _, e, mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr he'.1,
        by linarith [hPc v hv]⟩, he'.2⟩
    have hsplit' := hsplit (le_refl top)
    have hlt' := card_cut_lt_le regular hmed hPc htop
    have hend := card_endpoints_le ({e ∈ H.edgeFinset | top ≤ score e} : Finset _)
    have hhigh' := hsub (fun e => top ≤ score e)
    have hmid : #{e ∈ H.cutFinset P | top ≤ score e ∧ score e < top} = 0 := by
      simp
    have hnat : #(H.cutFinset P) ≤ 3 * #{e ∈ H.edgeFinset | top ≤ score e} := by lia
    exact (by exact_mod_cast hnat : (#(H.cutFinset P) : ℝ) ≤ _).trans high
  -- Inside the grid: `t = a + i δ ≤ m < a + (i + 1) δ`.
  obtain ⟨i, hiM, ht, ht'⟩ := exists_grid_index hδ (M := M) hge hlt
  set t := a + i * δ
  set t' := a + (i + 1) * δ
  set window : Finset (Sym2 W) := {e ∈ H.edgeFinset | t ≤ score e ∧ score e < t'}
  set S : Finset W := {v | EdgeStraddles H score t v}
  -- Charged vertices outside `P` straddle `t`.
  have hV : #{v | v ∉ P ∧ ∃ e ∈ H.incidenceFinset v, score e < t} ≤ #(S.filter (· ∉ P)) := by
    refine card_le_card fun v hv => ?_
    obtain ⟨hv, e, he, hlt⟩ := (mem_filter.mp hv).2
    obtain ⟨e', he', hge⟩ := exists_ge_med hmed v
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, e, he, hlt, e', he',
      by linarith [hPc v hv]⟩, hv⟩
  -- Charged vertices inside `P` straddle `t` or are endpoints of window edges.
  have hU : #{u | u ∈ P ∧ ∃ e ∈ H.incidenceFinset u, t' ≤ score e} ≤
      #(S.filter (· ∈ P)) + #{w | ∃ e ∈ window, w ∈ e} := by
    refine (card_le_card fun u hu => ?_).trans (card_union_le _ _)
    obtain ⟨hu, e, he, hge⟩ := (mem_filter.mp hu).2
    obtain ⟨f, hf, hfle⟩ := exists_le_med hmed u
    have hmu := hP u hu
    by_cases hlow : score f < t
    · exact mem_union_left _ (mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, f, hf, hlow, e, he, by linarith⟩, hu⟩)
    · have hf2 := SimpleGraph.mem_incidenceFinset.mp hf
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, f, mem_filter.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr hf2.1, not_lt.mp hlow, by linarith⟩, hf2.2⟩)
  have hsplit' := hsplit (show t ≤ t' by linarith)
  have hlt' := card_cut_lt_le regular hmed hPc ht
  have hge' := card_cut_ge_le regular hmed hP ht'
  have hend := card_endpoints_le window
  have hwin := hsub (fun e => t ≤ score e ∧ score e < t')
  have hS := card_filter_add_card_filter_not (s := S) (· ∈ P)
  have hnat : #(H.cutFinset P) ≤ #S + 3 * #window := by
    simp only [window] at *
    lia
  calc (#(H.cutFinset P) : ℝ) ≤ #S + 3 * #window := by exact_mod_cast hnat
    _ ≤ B := mid i hiM

end Cut

/-! ### The layout -/

/-- **The median layout.** Score the edges of a cubic graph and fix a grid
`a, a + δ, ..., a + M δ`. If three times the edges in each tail, and the vertices straddling
each grid threshold plus three times the edges scoring in the following window, are at most
`B`, then listing the vertices by median score gives a layout all of whose prefixes are crossed
by at most `B` edges. -/
theorem exists_key_of_edgeScore (regular : H.IsRegularOfDegree 3) (score : Sym2 W → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 3 * (#{e ∈ H.edgeFinset | score e < a} : ℝ) ≤ B)
    (high : 3 * (#{e ∈ H.edgeFinset | a + M * δ ≤ score e} : ℝ) ≤ B)
    (mid : ∀ i < M, (#{v | EdgeStraddles H score (a + i * δ) v} : ℝ) +
      3 * (#{e ∈ H.edgeFinset | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ} : ℝ) ≤ B) :
    ∃ key : W → ℕ, Function.Injective key ∧
      ∀ t : ℕ, (#(H.cutFinset {w | key w < t}) : ℝ) ≤ B := by
  choose med hmed using exists_isMedian regular score
  -- List the vertices by median, breaking ties by a fixed enumeration.
  obtain ⟨key, hinj, hkey⟩ := exists_key_of_score med
  refine ⟨key, hinj, fun t => ?_⟩
  rcases hkey t with hempty | ⟨m, hP, hPc⟩
  · have hB : (0 : ℝ) ≤ B := le_trans (by positivity) low
    have : ({w | key w < t} : Finset W) = ∅ := filter_eq_empty_iff.mpr fun w _ => hempty w
    simpa [this, SimpleGraph.cutFinset] using hB
  · exact card_cutFinset_le regular hmed (P := {w | key w < t}) (m := m)
      (fun v hv => hP v (mem_filter.mp hv).2)
      (fun v hv => hPc v fun h => hv (mem_filter.mpr ⟨mem_univ _, h⟩)) hδ M low high mid

end Proofs
