/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Compression
public import Proofs.Layouts.Cubic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

/-!
# Compressing to a simple cubic quotient

A terminal compression in degree at most four has no parallel edges between blocks. In
degree three its nontrivial quotient is cubic and has at most twice the original cycle rank
vertices. Expanding a cubic layout gives the subcubic layout bound, with logarithmic overhead.
-/

@[expose] public section

namespace Proofs

open Set

variable {V E : Type*}

namespace Multigraph

variable {G : Multigraph V E}

namespace Compression

variable {d : ℕ} (c : Compression G d)

/-- A compression is *final* when adjacent blocks are joined by only one edge and at least
three edges leave every block with a neighbouring block. -/
def Final : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty →
      (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).ncard ≤ 1 ∧
        3 ≤ (G.cut {v | v ∈ B}).ncard

/-- Up to degree four a terminal compression is final: two edges between adjacent blocks
would let them merge, and a block with fewer than three outgoing edges would merge with a
neighbour. -/
theorem Terminal.final [Finite E] (hc : c.Terminal) (hd : d ≤ 4) : c.Final := by
  intro B hB B' hB' hne hjoin
  have hdis : Disjoint {v | v ∈ B} {v | v ∈ B'} :=
    disjoint_left.mpr fun v hv hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hsum := G.ncard_cut_union_add hdis
  have hlt := hc B hB B' hB' hne hjoin
  have hBdeg := c.cut_le B hB
  have hB'deg := c.cut_le B' hB'
  have hpos := hjoin.ncard_pos
  constructor <;> lia

/-- Every multigraph of maximum degree three has a final compression. -/
theorem exists_final [Finite V] [Finite E] (hG : G.MaxDegreeLE 3) :
    ∃ c : Compression G 3, c.Final :=
  (exists_terminal hG).imp fun c hc => Terminal.final c hc (by norm_num)

/-- The blocks at the two ends of an edge. -/
noncomputable def ends (e : E) : Sym2 c.blocks :=
  s(c.blockOf (G.src e), c.blockOf (G.tgt e))

/-- The *quotient* of a compression: the simple graph on the blocks in which two distinct
blocks are adjacent when an edge joins them. -/
def quotient : SimpleGraph c.blocks where
  Adj B B' := B ≠ B' ∧ ∃ e, c.ends e = s(B, B')
  symm := ⟨fun _ _ ⟨h, e, he⟩ => ⟨h.symm, e, he.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The ends of an edge form an edge of the quotient exactly when they are distinct blocks. -/
theorem ends_mem_edgeSet {e : E} :
    c.ends e ∈ c.quotient.edgeSet ↔ c.blockOf (G.src e) ≠ c.blockOf (G.tgt e) :=
  ⟨fun h => h.1, fun h => ⟨h, e, rfl⟩⟩

/-- The edges of the quotient are the ends of the edges of `G` between distinct blocks. -/
theorem edgeSet_quotient :
    c.quotient.edgeSet = c.ends '' {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)} := by
  ext s
  induction s using Sym2.ind
  simp only [SimpleGraph.mem_edgeSet, quotient, Set.mem_image, Set.mem_ofPred_eq]
  grind [ends, Sym2.eq_iff]

/-- In a final compression, an edge between two distinct blocks is determined by its ends. -/
theorem injOn_ends [Finite E] (hc : c.Final) :
    InjOn c.ends {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)} := by
  intro e₁ (h₁ : c.blockOf (G.src e₁) ≠ c.blockOf (G.tgt e₁)) e₂ _ h
  have hS (e : E) (he : c.ends e = c.ends e₁) : e ∈ G.cut {v | v ∈ (c.blockOf (G.src e₁)).1} ∩
      G.cut {v | v ∈ (c.blockOf (G.tgt e₁)).1} := by
    rcases Sym2.eq_iff.1 he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
      simp [mem_cut, mem_iff_blockOf_eq, hs, ht, h₁, Ne.symm h₁]
  have := (hc _ (c.blockOf (G.src e₁)).2 _ (c.blockOf (G.tgt e₁)).2
    (fun h => h₁ (Subtype.ext h)) ⟨e₁, hS e₁ rfl⟩).1
  exact (ncard_le_one (toFinite _)).1 this _ (hS e₁ rfl) _ (hS e₂ h.symm)

/-- In a final compression, the quotient degree equals the block's boundary size. -/
theorem degree_eq_cut [Finite E] (hc : c.Final) [c.quotient.LocallyFinite] (B : c.blocks) :
    c.quotient.degree B = (G.cut {v | v ∈ B.1}).ncard := by
  rw [← SimpleGraph.ncard_incidenceSet]
  have : c.quotient.incidenceSet B = c.ends '' G.cut {v | v ∈ B.1} := by
    ext s
    simp only [SimpleGraph.incidenceSet, edgeSet_quotient, mem_image]
    simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq]
    grind [ends]
  rw [this, ((c.injOn_ends hc).mono fun _ he => c.external_of_cut he).ncard_image]

/-- The cut of a union of whole blocks embeds in the quotient's cut. -/
theorem ncard_cut_le [Finite E] (hc : c.Final) [Fintype c.quotient.edgeSet]
    (T : Finset c.blocks) :
    (G.cut {v | c.blockOf v ∈ T}).ncard ≤ (c.quotient.cutFinset T).card := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn c.ends (fun e he => ?_)
    ((c.injOn_ends hc).mono fun e he => ?_)
  · rw [mem_cut, mem_ofPred_eq, mem_ofPred_eq] at he
    rw [Finset.mem_coe, ends, SimpleGraph.mem_cutFinset_mk]
    exact ⟨c.ends_mem_edgeSet.2 fun h => he (by rw [h]), by tauto⟩
  · intro h
    rw [mem_cut, mem_ofPred_eq, mem_ofPred_eq, h] at he
    exact he Iff.rfl

/-- In a final compression the cut of the core is at most the cut of the quotient. -/
theorem ncard_cut_multiQuotient_le [Finite E] (hc : c.Final) [Fintype c.quotient.edgeSet]
    (p : c.blocks → Prop) [DecidablePred p] :
    (c.multiQuotient.cut {B | p B}).ncard ≤
      (c.quotient.cutFinset (Finset.univ.filter p)).card := by
  rw [← c.ncard_cut_multiQuotient]
  simpa using c.ncard_cut_le hc (Finset.univ.filter p)

/-- The quotient has at most `(h choose 2)` edges, for `h` blocks, so no cut has more. -/
theorem card_cutFinset_le_choose [Fintype c.quotient.edgeSet] (T : Finset c.blocks) :
    (c.quotient.cutFinset T).card ≤ (Fintype.card c.blocks).choose 2 :=
  (Finset.card_le_card (SimpleGraph.cutFinset_subset_edgeFinset T)).trans
    SimpleGraph.card_edgeFinset_le_card_choose_two

/-! ### Cubic compressions -/

section Cubic

variable (c : Compression G 3)

/-- In a final compression of a connected multigraph with at least two blocks, exactly three
edges leave every block. -/
theorem ncard_cut_eq_three [Finite E] (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) (B : c.blocks) : (G.cut {v | v ∈ B.1}).ncard = 3 := by
  obtain ⟨e, he, B', hB', he'⟩ := c.exists_cut_other_block hG two B
  exact le_antisymm (c.cut_le _ B.2)
    (hc _ B.2 _ B'.2 (fun h => hB' (Subtype.ext h).symm) ⟨e, he, he'⟩).2

/-- The quotient of a final cubic compression is regular. -/
theorem isRegularOfDegree [Finite E] (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) [c.quotient.LocallyFinite] : c.quotient.IsRegularOfDegree 3 := by
  intro B
  exact (c.degree_eq_cut hc B).trans (c.ncard_cut_eq_three hc hG two B)

/-- **The size of the quotient.** A final compression of a connected multigraph with `N`
vertices and `M` edges into `h ≥ 2` blocks has `h + 2N ≤ 2M`. -/
theorem card_add_two_mul_le [Finite E] (hc : c.Final) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) : c.blocks.card + 2 * Nat.card V ≤ 2 * Nat.card E := by
  classical
  have hdeg := c.quotient.sum_degrees_eq_twice_card_edges
  simp only [(c.isRegularOfDegree hc hG two).degree_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, smul_eq_mul] at hdeg
  have hE : c.quotient.edgeFinset.card = c.External.ncard := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, edgeSet_quotient,
      (c.injOn_ends hc).ncard_image]
    rfl
  have := c.external_add_vertices_le
  lia

/-- A final compression of a connected multigraph with at least two blocks has at most `2 β₁`
blocks. -/
theorem card_blocks_le [Finite E] (hc : c.Final) (hG : G.Connected) (two : 2 ≤ c.blocks.card) :
    c.blocks.card ≤ 2 * G.cycleRank := by
  have := c.card_add_two_mul_le hc hG two
  unfold Multigraph.cycleRank
  lia

end Cubic

end Compression

end Multigraph

/-! ### The layout bound -/

/-- **Compression with logarithmic overhead.** A cubic coefficient `c` gives connected
subcubic multigraph layouts of width `(2c + η) β₁ + 3 log₂ |V| + C`. -/
theorem CubicLayoutBound.exists_layout_log {c : ℝ} (h : CubicLayoutBound c) (hc : 0 ≤ c)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Connected → G.MaxDegreeLE 3 → ∃ π : Layout V, ∀ t,
        ((G.cut (π.initial t)).ncard : ℝ) ≤
          (2 * c + η) * G.cycleRank + 3 * Nat.log 2 (Nat.card V) + C := by
  obtain ⟨N₀, hN₀⟩ := h (η / 2) (by positivity)
  refine ⟨(N₀ + 1).choose 2 + 5, fun V E _ _ G hG hdeg => ?_⟩
  classical
  have := Fintype.ofFinite V
  obtain ⟨Q, hQ⟩ := Multigraph.Compression.exists_final hdeg
  have hβ : 0 ≤ (2 * c + η) * G.cycleRank := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hC : (0 : ℝ) ≤ (N₀ + 1).choose 2 := Nat.cast_nonneg _
  obtain ⟨key, hkey, hX⟩ : ∃ key : Q.blocks → ℕ, key.Injective ∧ ∀ q,
      ((Q.quotient.cutFinset (Finset.univ.filter fun B => key B < q)).card : ℝ) ≤
        (2 * c + η) * G.cycleRank + ((N₀ + 1).choose 2 + 2) := by
    by_cases hbig : 2 ≤ Q.blocks.card ∧ N₀ < Q.blocks.card
    · -- A large quotient is laid out by the cubic layout bound; it has at most `2 β₁` vertices.
      obtain ⟨key, hkey, hcut⟩ := hN₀ Q.blocks Q.quotient (Q.isRegularOfDegree hQ hG hbig.1)
        (by rw [Fintype.card_coe]; exact hbig.2)
      have hsize : (Fintype.card Q.blocks : ℝ) ≤ 2 * G.cycleRank := by
        rw [Fintype.card_coe]
        exact_mod_cast Q.card_blocks_le hQ hG hbig.1
      have := mul_le_mul_of_nonneg_left hsize (by linarith : (0 : ℝ) ≤ c + η / 2)
      exact ⟨key, hkey, fun q => (hcut q).trans (by linarith)⟩
    · -- A small quotient has at most `(N₀ + 1).choose 2` edges.
      refine ⟨fun B => Fintype.equivFin _ B, fun B B' h => (Fintype.equivFin _).injective
        (Fin.ext h), fun q => (Nat.cast_le.2 ?_).trans (by linarith)⟩
      exact (Q.card_cutFinset_le_choose _).trans
        (Nat.choose_le_choose 2 (by rw [Fintype.card_coe]; lia))
  obtain ⟨π, hπ⟩ := Q.exists_layout hkey fun q =>
    (Nat.cast_le.mpr (Q.ncard_cut_multiQuotient_le hQ fun B => key B < q)).trans (hX q)
  push_cast at hπ
  exact ⟨π, fun t => by linarith [hπ t]⟩

/-- **From cubic graphs to subcubic multigraphs.** A cubic layout bound with coefficient `c`
gives the layout bound for maximum degree three with coefficient `2c`. -/
theorem LayoutBound.of_cubic {c : ℝ} (hc : 0 ≤ c) (h : CubicLayoutBound c) :
    LayoutBound 3 (2 * c) := by
  intro η hη
  obtain ⟨C, hC⟩ := h.exists_layout_log hc hη
  obtain ⟨K, hK⟩ := exists_log_le_mul_add (ε := η / 3) (by positivity)
  refine ⟨C + 3 * K, fun V E _ _ G hG hdeg => ?_⟩
  obtain ⟨π, hπ⟩ := hC V E G hG hdeg
  exact ⟨π, fun t => by linarith [hπ t, hK (Nat.card V)]⟩

end Proofs
