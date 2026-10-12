/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Support
public import Proofs.Layouts.Scores
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith

/-!
# Compressing a graph to its core

A connected multigraph `G` of maximum degree `d` is compressed by merging adjacent blocks of
vertices while the merged block keeps at most `d` outgoing edges. Throughout, `G` has `N`
vertices, `M` edges, and cycle rank `β₁ = M - N + 1`.

**Compression.** Partition the vertices into *blocks*, each listing its vertices in order,
starting from single vertices. Two distinct blocks joined by an edge are *merged* when their
union still has at most `d` edges leaving it; the merged block lists the longer block first.
A `Compression` records the invariants of this process:

* at most `d` edges leave a block;
* at most `d log₂ |B|` edges leave a proper prefix of a block `B`. A proper prefix of a merged
  block is a proper prefix of its first part, or all of its first part followed by a proper
  prefix of its second part, which has at most half as many vertices;
* there are at least as many blocks and edges inside blocks as vertices, since a merge loses
  one block and moves at least one edge inside.

Each merge loses a block, so merging ends in a *terminal* compression, in which no adjacent
pair can merge (`exists_terminal`).

**The core.** The `multiQuotient` keeps every edge between distinct blocks; it is a loopless
multigraph of maximum degree `d`, and the terminal core satisfies the density estimate
`(2d - 3) |E(core)| ≤ 3d β₁` (`Terminal.multi_edge_bound`).

**Expansion.** Lay out `G` block by block, ordering the blocks by a layout of the quotient and
each block by its list. A frontier consists of whole blocks followed by a prefix of one more
block: the edges leaving the whole blocks are edges of the quotient crossing its frontier, and
at most `d log₂ N + d` edges leave the prefix (`exists_layout`).

## Main definitions

* `Proofs.Multigraph.Compression`: a partition into ordered blocks, with its invariants.
* `Proofs.Multigraph.Compression.Terminal`: no merge applies.
* `Proofs.Multigraph.Compression.multiQuotient`: the core, the multigraph on the blocks
  retaining every edge between blocks.

## Main results

* `Proofs.Multigraph.Compression.exists_terminal`: merging terminates.
* `Proofs.Multigraph.Compression.Terminal.multi_edge_bound`: the core density.
* `Proofs.Multigraph.Compression.exists_layout`: expanding a layout of the core.
-/

@[expose] public section

namespace Proofs

open Set

variable {V E : Type*}

/-! ### Preliminaries -/

/-- `log₂ N` is at most `ε N` plus a constant. -/
theorem exists_log_le_mul_add {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ N : ℕ, (Nat.log 2 N : ℝ) ≤ ε * N + K := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ε) one_lt_two
  refine ⟨k, fun N => ?_⟩
  have hN : 2 ^ k * (Nat.log 2 N - k) ≤ N := by
    rcases le_or_gt (Nat.log 2 N) k with h | h
    · simp [Nat.sub_eq_zero_of_le h]
    · calc 2 ^ k * (Nat.log 2 N - k) ≤ 2 ^ k * 2 ^ (Nat.log 2 N - k) :=
            Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le
        _ = 2 ^ Nat.log 2 N := by rw [← pow_add, Nat.add_sub_cancel' h.le]
        _ ≤ N := Nat.pow_log_le_self 2 (by rintro rfl; simp at h)
  have h₁ : (Nat.log 2 N : ℝ) ≤ ((Nat.log 2 N - k : ℕ) : ℝ) + k := by norm_cast; lia
  have h₂ : (2 : ℝ) ^ k * ((Nat.log 2 N - k : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have h₃ : 1 < ε * 2 ^ k := by rwa [div_lt_iff₀ hε, mul_comm] at hk
  nlinarith [mul_le_mul_of_nonneg_left h₂ hε.le,
    mul_le_mul_of_nonneg_right h₃.le (Nat.cast_nonneg (α := ℝ) (Nat.log 2 N - k))]

namespace Multigraph

variable {G : Multigraph V E}

/-- Cuts are subadditive. -/
theorem cut_union_subset (G : Multigraph V E) (S T : Set V) :
    G.cut (S ∪ T) ⊆ G.cut S ∪ G.cut T := by
  intro e
  simp only [mem_cut, mem_union]
  tauto

/-- The cut of a disjoint union: the edges leaving both parts are counted twice on the right
and not at all on the left. -/
theorem ncard_cut_union_add [Finite E] (G : Multigraph V E) {S T : Set V} (h : Disjoint S T) :
    (G.cut (S ∪ T)).ncard + 2 * (G.cut S ∩ G.cut T).ncard =
      (G.cut S).ncard + (G.cut T).ncard := by
  have hd := Set.disjoint_left.1 h
  have h₁ : G.cut (S ∪ T) ∪ (G.cut S ∩ G.cut T) = G.cut S ∪ G.cut T := by
    ext e
    simp only [mem_union, mem_inter_iff, mem_cut]
    grind
  have h₂ : Disjoint (G.cut (S ∪ T)) (G.cut S ∩ G.cut T) := by
    refine Set.disjoint_left.2 fun e he he' => ?_
    simp only [mem_union, mem_inter_iff, mem_cut] at he he'
    grind
  have := Set.ncard_union_add_ncard_inter (G.cut S) (G.cut T)
  rw [← h₁, Set.ncard_union_eq h₂] at this
  lia

/-- In a connected multigraph, some edge leaves every set of vertices other than the empty set
and the whole vertex set. -/
theorem Connected.cut_nonempty (hG : G.Connected) {S : Set V} {u v : V} (hu : u ∈ S)
    (hv : v ∉ S) : (G.cut S).Nonempty := by
  by_contra h
  have key (w : V) (hw : Relation.ReflTransGen G.Adj u w) : w ∈ S := by
    induction hw with
    | refl => exact hu
    | tail _ hab ih =>
      obtain ⟨e, he⟩ := hab
      have : e ∉ G.cut S := fun he => h ⟨e, he⟩
      grind [mem_cut]
  exact hv (key v (hG u v))

/-! ### Compressions -/

/-- A *compression* of `G`: a partition of its vertices into *blocks*, each listing its
vertices in order, with the invariants maintained by merging. A block `B` is identified with
its vertex set `{v | v ∈ B}`. -/
structure Compression (G : Multigraph V E) (d : ℕ) where
  /-- The blocks. -/
  blocks : Finset (List V)
  /-- Every vertex lies in a block. -/
  cover : ∀ v, ∃ B ∈ blocks, v ∈ B
  /-- Blocks sharing a vertex are equal. -/
  eq_of_mem : ∀ B ∈ blocks, ∀ B' ∈ blocks, ∀ v ∈ B, v ∈ B' → B = B'
  /-- A block lists each of its vertices once. -/
  nodup : ∀ B ∈ blocks, B.Nodup
  /-- Blocks are nonempty. -/
  ne_nil : ∀ B ∈ blocks, B ≠ []
  /-- At most `d` edges leave a block. -/
  cut_le : ∀ B ∈ blocks, (G.cut {v | v ∈ B}).ncard ≤ d
  /-- At most `d log₂ |B|` edges leave a proper prefix of a block `B`. -/
  cut_take_le : ∀ B ∈ blocks, ∀ k < B.length,
    (G.cut {v | v ∈ B.take k}).ncard ≤ d * Nat.log 2 B.length
  /-- There are at least as many blocks and edges inside blocks as vertices. -/
  card_le : Nat.card V ≤
    blocks.card + {e | ∃ B ∈ blocks, G.src e ∈ B ∧ G.tgt e ∈ B}.ncard

namespace Compression

section General

variable {d : ℕ} (c : Compression G d)

/-! ### Merging -/

/-- The blocks after merging `B` and `B'`: their concatenation replaces them. -/
def mergeBlocks [DecidableEq V] (B B' : List V) : Finset (List V) :=
  insert (B ++ B') ((c.blocks.erase B).erase B')

theorem mem_mergeBlocks [DecidableEq V] {B B' C : List V} :
    C ∈ c.mergeBlocks B B' ↔ C = B ++ B' ∨ (C ≠ B' ∧ C ≠ B ∧ C ∈ c.blocks) := by
  simp only [mergeBlocks, Finset.mem_insert, Finset.mem_erase]

/-- Every old block lies inside a merged block. -/
theorem exists_mem_mergeBlocks [DecidableEq V] (B B' : List V) {C : List V}
    (hC : C ∈ c.blocks) :
    ∃ D ∈ c.mergeBlocks B B', ∀ v ∈ C, v ∈ D := by
  by_cases hB : C = B
  · exact ⟨B ++ B', c.mem_mergeBlocks.2 (Or.inl rfl),
      fun v hv => List.mem_append_left _ (hB ▸ hv)⟩
  by_cases hB' : C = B'
  · exact ⟨B ++ B', c.mem_mergeBlocks.2 (Or.inl rfl),
      fun v hv => List.mem_append_right _ (hB' ▸ hv)⟩
  exact ⟨C, c.mem_mergeBlocks.2 (Or.inr ⟨hB', hB, hC⟩), fun _ hv => hv⟩

/-- Merging two distinct blocks loses one block. -/
theorem card_mergeBlocks [DecidableEq V] {B B' : List V} (hB : B ∈ c.blocks)
    (hB' : B' ∈ c.blocks) (hne : B ≠ B') : (c.mergeBlocks B B').card + 1 = c.blocks.card := by
  have hnot : B ++ B' ∉ (c.blocks.erase B).erase B' := by
    intro h
    simp only [Finset.mem_erase] at h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B (c.ne_nil B hB)
    exact h.2.1 (c.eq_of_mem _ h.2.2 B hB v (List.mem_append_left _ hv) hv)
  rw [mergeBlocks, Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem
    (Finset.mem_erase.2 ⟨hne.symm, hB'⟩), Finset.card_erase_of_mem hB]
  have := Finset.one_lt_card.2 ⟨B, hB, B', hB', hne⟩
  lia

/-- A proper prefix of `B ++ B'`, with `B'` no longer than `B`, has at most
`d log₂ |B ++ B'|` outgoing edges: it is a proper prefix of `B`, or all of `B` followed by a
proper prefix of `B'`, and `2 |B'| ≤ |B ++ B'|`. -/
theorem cut_take_append_le [Finite E] {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks)
    (hlen : B'.length ≤ B.length) {k : ℕ} (hk : k < (B ++ B').length) :
    (G.cut {v | v ∈ (B ++ B').take k}).ncard ≤ d * Nat.log 2 (B ++ B').length := by
  rw [List.length_append] at hk ⊢
  rw [List.take_append]
  rcases lt_or_ge k B.length with hk' | hk'
  · rw [Nat.sub_eq_zero_of_le hk'.le, List.take_zero, List.append_nil]
    exact (c.cut_take_le B hB k hk').trans
      (Nat.mul_le_mul_left d (Nat.log_mono_right (by lia)))
  · rw [List.take_of_length_le hk']
    have hb : B'.length ≠ 0 := by lia
    have h₁ := Set.ncard_le_ncard (G.cut_union_subset {v | v ∈ B}
      {v | v ∈ B'.take (k - B.length)})
    have h₂ := Set.ncard_union_le (G.cut {v | v ∈ B})
      (G.cut {v | v ∈ B'.take (k - B.length)})
    have h₃ := c.cut_le B hB
    have h₄ := c.cut_take_le B' hB' (k - B.length) (by lia)
    have h₅ : Nat.log 2 B'.length + 1 ≤ Nat.log 2 (B.length + B'.length) := by
      rw [← Nat.log_mul_base one_lt_two hb]
      exact Nat.log_mono_right (by lia)
    have h₆ := Nat.mul_le_mul_left d h₅
    simp only [Nat.mul_add, Nat.mul_one] at h₆
    rw [show {v | v ∈ B ++ B'.take (k - B.length)} =
      {v | v ∈ B} ∪ {v | v ∈ B'.take (k - B.length)} from Set.ext fun _ => List.mem_append]
    lia

/-- Merging two blocks joined by an edge moves that edge inside a block, so the blocks and the
inside edges of the merged partition still number at least the vertices. -/
theorem card_le_mergeBlocks [DecidableEq V] [Finite E] {B B' : List V} (hB : B ∈ c.blocks)
    (hB' : B' ∈ c.blocks) (hne : B ≠ B')
    (hjoin : (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty) :
    Nat.card V ≤ (c.mergeBlocks B B').card +
      {e | ∃ D ∈ c.mergeBlocks B B', G.src e ∈ D ∧ G.tgt e ∈ D}.ncard := by
  have hd (v : V) (hv : v ∈ B) : v ∉ B' := fun hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hsub : {e | ∃ D ∈ c.blocks, G.src e ∈ D ∧ G.tgt e ∈ D} ∪
      (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}) ⊆
        {e | ∃ D ∈ c.mergeBlocks B B', G.src e ∈ D ∧ G.tgt e ∈ D} := by
    rintro e (⟨C, hC, hs, ht⟩ | ⟨h₁, h₂⟩)
    · obtain ⟨D, hD, hCD⟩ := c.exists_mem_mergeBlocks B B' hC
      exact ⟨D, hD, hCD _ hs, hCD _ ht⟩
    · refine ⟨B ++ B', c.mem_mergeBlocks.2 (Or.inl rfl), ?_⟩
      have := hd (G.src e)
      have := hd (G.tgt e)
      simp only [mem_cut, mem_ofPred_eq] at h₁ h₂
      simp only [List.mem_append]
      tauto
  have hdisj : Disjoint {e | ∃ D ∈ c.blocks, G.src e ∈ D ∧ G.tgt e ∈ D}
      (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}) := by
    apply Set.disjoint_left.2
    simp only [mem_ofPred_eq, mem_inter_iff, mem_cut]
    grind [c.eq_of_mem]
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hdisj] at this
  have := hjoin.ncard_pos
  have := c.card_le
  have := c.card_mergeBlocks hB hB' hne
  lia

/-- **Merging.** Two distinct blocks joined by an edge, whose union has at most `d` edges
leaving it, may be replaced by their union, listing the longer block first. -/
theorem exists_merge [Finite E] {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks)
    (hne : B ≠ B') (hjoin : (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty)
    (hcut : (G.cut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ≤ d) :
    ∃ c' : Compression G d, c'.blocks.card < c.blocks.card := by
  classical
  wlog hlen : B'.length ≤ B.length generalizing B B'
  · rw [inter_comm] at hjoin
    rw [union_comm] at hcut
    exact this hB' hB hne.symm hjoin hcut (by lia)
  have hd (v : V) (hv : v ∈ B) : v ∉ B' := fun hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  refine ⟨{ blocks := c.mergeBlocks B B'
            cover := ?_, eq_of_mem := ?_, nodup := ?_, ne_nil := ?_, cut_le := ?_
            cut_take_le := ?_, card_le := c.card_le_mergeBlocks hB hB' hne hjoin },
    Nat.lt_of_succ_le (c.card_mergeBlocks hB hB' hne).le⟩
  · intro v
    obtain ⟨C, hC, hv⟩ := c.cover v
    obtain ⟨D, hD, hCD⟩ := c.exists_mem_mergeBlocks B B' hC
    exact ⟨D, hD, hCD v hv⟩
  · simp only [mem_mergeBlocks]
    grind [c.eq_of_mem]
  · simp only [mem_mergeBlocks]
    rintro C (rfl | ⟨-, -, hC⟩)
    · exact List.nodup_append.2 ⟨c.nodup B hB, c.nodup B' hB',
        fun a ha b hb hab => hd a ha (hab ▸ hb)⟩
    · exact c.nodup C hC
  · simp only [mem_mergeBlocks]
    rintro C (rfl | ⟨-, -, hC⟩)
    · exact List.append_ne_nil_of_left_ne_nil (c.ne_nil B hB) _
    · exact c.ne_nil C hC
  · simp only [mem_mergeBlocks]
    rintro C (rfl | ⟨-, -, hC⟩)
    · rwa [show {v | v ∈ B ++ B'} = {v | v ∈ B} ∪ {v | v ∈ B'} from
        Set.ext fun _ => List.mem_append]
    · exact c.cut_le C hC
  · simp only [mem_mergeBlocks]
    rintro C (rfl | ⟨-, -, hC⟩) k hk
    · exact c.cut_take_append_le hB hB' hlen hk
    · exact c.cut_take_le C hC k hk

/-- The initial compression: every vertex is a block of its own. -/
def initial [Fintype V] [DecidableEq V] [Finite E] (hG : G.MaxDegreeLE d) :
    Compression G d where
  blocks := Finset.univ.image fun v => [v]
  cover v := ⟨[v], Finset.mem_image_of_mem _ (Finset.mem_univ v), List.mem_singleton_self v⟩
  eq_of_mem := by simp
  nodup := by simp
  ne_nil := by simp
  cut_le := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, List.mem_singleton]
    intro v
    refine (Set.ncard_le_ncard fun e he => ?_).trans (hG v)
    simp only [mem_cut, mem_ofPred_eq] at he
    change G.src e = v ∨ G.tgt e = v
    tauto
  cut_take_le := by simp
  card_le := by
    rw [Finset.card_image_of_injective _ List.singleton_injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
    exact Nat.le_add_right _ _

end General

variable {d : ℕ} (c : Compression G d)

/-- No adjacent pair of blocks can still be merged within the degree budget. -/
def Terminal : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.cut {v | v ∈ B} ∩ G.cut {v | v ∈ B'}).Nonempty →
      d < (G.cut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard

/-- **Merging terminates.** A compression with the fewest blocks is terminal. -/
theorem exists_terminal [Finite V] [Finite E] (hG : G.MaxDegreeLE d) :
    ∃ c : Compression G d, c.Terminal := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c, -, hmin⟩ := (measure fun c : Compression G d => c.blocks.card).wf.has_min univ
    ⟨initial hG, trivial⟩
  refine ⟨c, fun B hB B' hB' hne hjoin => ?_⟩
  by_contra! h
  obtain ⟨c', hc'⟩ := c.exists_merge hB hB' hne hjoin h
  exact hmin c' trivial hc'

/-! ### The quotients -/

/-- The block containing a vertex. -/
noncomputable def blockOf (v : V) : c.blocks :=
  ⟨(c.cover v).choose, (c.cover v).choose_spec.1⟩

/-- A vertex lies in a block exactly when that block is its block. -/
theorem mem_iff_blockOf_eq {v : V} {B : c.blocks} : v ∈ B.1 ↔ c.blockOf v = B :=
  ⟨fun h => Subtype.ext (c.eq_of_mem _ (c.blockOf v).2 _ B.2 v (c.cover v).choose_spec.2 h),
    fun h => h ▸ (c.cover v).choose_spec.2⟩

/-- Edges whose endpoints lie in different blocks. -/
def External : Set E := {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}

/-- The *core*: the multigraph on the blocks retaining every edge between distinct blocks. -/
noncomputable def multiQuotient : Multigraph c.blocks c.External where
  src e := c.blockOf (G.src e.1)
  tgt e := c.blockOf (G.tgt e.1)

/-- The core has no loops. -/
theorem multiQuotient_loopless : c.multiQuotient.Loopless := fun e => e.2

/-- An edge leaving a block joins two distinct blocks. -/
theorem external_of_cut {B : c.blocks} {e : E} (he : e ∈ G.cut {v | v ∈ B.1}) :
    e ∈ c.External := by
  simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he
  grind [External]

/-- The degree of a block in the core is the number of edges leaving it. -/
theorem ncard_edgesAt_multiQuotient (B : c.blocks) :
    (c.multiQuotient.edgesAt B).ncard = (G.cut {v | v ∈ B.1}).ncard := by
  have heq : c.multiQuotient.edgesAt B =
      {e : c.External | e.1 ∈ G.cut {v | v ∈ B.1}} := by
    ext e
    simp only [edgesAt, Incident, multiQuotient, mem_ofPred_eq, mem_cut,
      mem_iff_blockOf_eq]
    have := e.2
    grind [External]
  rw [heq, ncard_subtype]
  congr 1
  exact inter_eq_left.mpr fun e he => c.external_of_cut he

/-- The core has maximum degree `d`. -/
theorem multiQuotient_maxDegreeLE : c.multiQuotient.MaxDegreeLE d := fun B =>
  (c.ncard_edgesAt_multiQuotient B).trans_le (c.cut_le _ B.2)

/-- The edges inside blocks are the complement of the external edges. -/
theorem inside_eq_compl :
    {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B} =
      c.Externalᶜ := by
  ext e
  simp only [External, mem_compl_iff, mem_ofPred_eq, not_not]
  constructor
  · rintro ⟨B, hB, hs, ht⟩
    rw [(c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).1 hs, (c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).1 ht]
  · intro h
    exact ⟨_, (c.blockOf (G.src e)).2, c.mem_iff_blockOf_eq.2 rfl,
      c.mem_iff_blockOf_eq.2 h.symm⟩

/-- Every merge moves at least one edge inside a block: the external edges and the vertices
together number at most the edges and the blocks. -/
theorem external_add_vertices_le [Finite E] :
    c.External.ncard + Nat.card V ≤ Nat.card E + c.blocks.card := by
  have htotal : c.External.ncard + c.Externalᶜ.ncard = Nat.card E :=
    ncard_add_ncard_compl c.External
  have hcard := c.card_le
  rw [inside_eq_compl] at hcard
  lia

/-- In a connected graph with at least two blocks, some edge leaves any block for another. -/
theorem exists_cut_other_block (hG : G.Connected) (two : 2 ≤ c.blocks.card) (B : c.blocks) :
    ∃ e ∈ G.cut {v | v ∈ B.1}, ∃ B' : c.blocks, B' ≠ B ∧ e ∈ G.cut {v | v ∈ B'.1} := by
  obtain ⟨B', hB', hne⟩ := Finset.exists_mem_ne two B.1
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B.2)
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ hB')
  obtain ⟨e, he⟩ := hG.cut_nonempty (S := {v | v ∈ B.1}) hu
    fun h => hne (c.eq_of_mem _ hB' _ B.2 w hw h)
  refine ⟨e, he, ?_⟩
  simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he ⊢
  by_cases h : c.blockOf (G.src e) = B
  · exact ⟨c.blockOf (G.tgt e), by grind, by grind⟩
  · exact ⟨c.blockOf (G.src e), h, by grind⟩

/-- In a terminal compression, the two ends of an edge of the core have degrees summing to at
least `d + 3`: their union has more than `d` outgoing edges, and the edges between them count
twice in the sum. -/
theorem Terminal.multi_degree_sum [Finite E] (hc : c.Terminal) (e : c.External) :
    d + 3 ≤ (c.multiQuotient.edgesAt (c.multiQuotient.src e)).ncard +
      (c.multiQuotient.edgesAt (c.multiQuotient.tgt e)).ncard := by
  let B := c.multiQuotient.src e
  let B' := c.multiQuotient.tgt e
  have hne : B ≠ B' := e.2
  have hne' : B.1 ≠ B'.1 := fun h => hne (Subtype.ext h)
  have hjoin : (G.cut {v | v ∈ B.1} ∩ G.cut {v | v ∈ B'.1}).Nonempty := by
    refine ⟨e.1, ?_⟩
    simp only [mem_inter_iff, mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq]
    change (¬(B = B ↔ B' = B)) ∧ ¬(B = B' ↔ B' = B')
    simp [hne, Ne.symm hne]
  have hdis : Disjoint {v | v ∈ B.1} {v | v ∈ B'.1} :=
    disjoint_left.mpr fun v hv hv' => hne' (c.eq_of_mem _ B.2 _ B'.2 v hv hv')
  have hsum := G.ncard_cut_union_add hdis
  have hlt := hc _ B.2 _ B'.2 hne' hjoin
  have hpos := hjoin.ncard_pos
  rw [c.ncard_edgesAt_multiQuotient, c.ncard_edgesAt_multiQuotient]
  change d + 3 ≤ (G.cut {v | v ∈ B.1}).ncard + (G.cut {v | v ∈ B'.1}).ncard
  lia

/-- In a terminal compression of a connected multigraph into at least two blocks, every block
has degree at least three in the core. -/
theorem Terminal.multi_degree_ge_three [Finite E] (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) (B : c.blocks) : 3 ≤ (c.multiQuotient.edgesAt B).ncard := by
  obtain ⟨e, he, -⟩ := c.exists_cut_other_block hG two B
  let e' : c.External := ⟨e, c.external_of_cut he⟩
  have hsum := Terminal.multi_degree_sum c hc e'
  have hs := c.multiQuotient_maxDegreeLE (c.multiQuotient.src e')
  have ht := c.multiQuotient_maxDegreeLE (c.multiQuotient.tgt e')
  have hi : c.multiQuotient.Incident B e' := by
    simp only [Incident, multiQuotient]
    simp only [mem_cut, mem_ofPred_eq, mem_iff_blockOf_eq] at he
    tauto
  rcases hi with h | h <;> rw [h] at hsum <;> lia

/-- A nontrivial terminal core has at least as many edges as blocks. -/
theorem Terminal.multi_blocks_le_edges [Finite E] (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) : c.blocks.card ≤ c.External.ncard := by
  let := Fintype.ofFinite c.External
  have hs := c.multiQuotient.sum_degree_mul c.multiQuotient_loopless (fun _ => 1)
  have hmin := Finset.sum_le_sum (s := Finset.univ)
    (fun B _ => Terminal.multi_degree_ge_three c hc hG two B)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe] at hs hmin
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hs
  lia

/-- **The core density.** The core of a terminal compression of a connected multigraph into at
least two blocks has at most `3d / (2d - 3)` times the cycle rank of `G` edges:
`(2d - 3) |E(core)| ≤ 3d β₁`. -/
theorem Terminal.multi_edge_bound [Finite E] (hc : c.Terminal) (hG : G.Connected)
    (two : 2 ≤ c.blocks.card) :
    (2 * d - 3) * c.External.ncard ≤ 3 * d * G.cycleRank := by
  let := Fintype.ofFinite c.External
  have hd := Multigraph.core_density c.multiQuotient c.multiQuotient_loopless
    (Terminal.multi_degree_ge_three c hc hG two) c.multiQuotient_maxDegreeLE
    (Terminal.multi_degree_sum c hc)
  rw [Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hd
  have hcard := c.external_add_vertices_le
  have hβ : Nat.card E + 1 ≤ G.cycleRank + Nat.card V := by
    unfold Multigraph.cycleRank
    lia
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := by
    have := (Terminal.multi_degree_ge_three c hc hG two
      ⟨_, (Finset.card_pos.mp (by lia : 0 < c.blocks.card)).choose_spec⟩).trans
        (c.multiQuotient_maxDegreeLE _)
    exact ⟨_, (Nat.sub_add_cancel this).symm⟩
  rw [show 2 * (k + 3) - 3 = 2 * k + 3 by lia]
  -- Multiply the vertex and cycle-rank inequalities by `3 d` and add the density estimate.
  have h₁ := Nat.mul_le_mul_left (3 * (k + 3)) hcard
  have h₂ := Nat.mul_le_mul_left (3 * (k + 3)) hβ
  linarith

/-- The cut of a union of whole blocks is the cut of the core. -/
theorem ncard_cut_multiQuotient [Finite E] (T : Set c.blocks) :
    (G.cut {v | c.blockOf v ∈ T}).ncard = (c.multiQuotient.cut T).ncard := by
  change (G.cut {v | c.blockOf v ∈ T}).ncard =
    {e : c.External | e.1 ∈ G.cut {v | c.blockOf v ∈ T}}.ncard
  rw [ncard_subtype]
  congr 1
  ext e
  grind [mem_cut, External]

/-! ### Expansion -/

/-- The position of a vertex in its block. -/
noncomputable def idx [DecidableEq V] (v : V) : ℕ :=
  (c.blockOf v).1.idxOf v

/-- At most `d log₂ N + d` edges leave the first `r` vertices of a block. -/
theorem ncard_cut_take_le [Finite V] [DecidableEq V] [Finite E] (B : c.blocks) (r : ℕ) :
    (G.cut {v | c.blockOf v = B ∧ c.idx v < r}).ncard ≤ d * Nat.log 2 (Nat.card V) + d := by
  have := Fintype.ofFinite V
  have : {v | c.blockOf v = B ∧ c.idx v < r} = {v | v ∈ B.1.take r} := by
    ext v
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨rfl, h⟩
      exact (List.mem_take_iff_idxOf_lt (c.mem_iff_blockOf_eq.2 rfl)).2 h
    · intro h
      have hv := List.mem_of_mem_take h
      obtain rfl := c.mem_iff_blockOf_eq.1 hv
      exact ⟨rfl, (List.mem_take_iff_idxOf_lt hv).1 h⟩
  rw [this]
  rcases lt_or_ge r B.1.length with h | h
  · have := c.cut_take_le _ B.2 r h
    have hlog := Nat.log_mono_right (b := 2)
      ((c.nodup _ B.2).length_le_card.trans_eq Nat.card_eq_fintype_card.symm)
    exact this.trans ((Nat.mul_le_mul_left d hlog).trans (Nat.le_add_right _ _))
  · rw [List.take_of_length_le h]
    have := c.cut_le _ B.2
    exact this.trans (Nat.le_add_left _ _)

/-- Lay out the vertices block by block, ordering the blocks by an injective key and each block
by its list. Every nonempty prefix of the layout consists of the vertices of the earlier blocks
and a prefix of one more block. -/
theorem exists_layout_prefixes [Finite V] [DecidableEq V] {key : c.blocks → ℕ}
    (hkey : key.Injective) :
    ∃ π : Layout V, ∀ t, π.initial t = ∅ ∨ ∃ B : c.blocks, ∃ r : ℕ,
      π.initial t = {v | key (c.blockOf v) < key B} ∪
        {v | c.blockOf v = B ∧ c.idx v < r} := by
  let := Fintype.ofFinite V
  let f (v : V) : ℕ ×ₗ ℕ := toLex (key (c.blockOf v), c.idx v)
  have hf : f.Injective := by
    intro v w h
    simp only [f, toLex_inj, Prod.mk.injEq] at h
    have hb := hkey h.1
    have hi := h.2
    rw [idx, idx, ← hb] at hi
    exact (List.idxOf_inj (c.mem_iff_blockOf_eq.mpr rfl)).mp hi
  obtain ⟨π, hπ⟩ := Layout.exists_monotone hf
  refine ⟨π, fun t => ?_⟩
  rcases (π.initial t).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  obtain ⟨v₀, hv₀, hmax⟩ := Set.exists_max_image _ f (toFinite _) h
  refine Or.inr ⟨c.blockOf v₀, c.idx v₀ + 1, ?_⟩
  ext v
  have : v ∈ π.initial t ↔ f v ≤ f v₀ :=
    ⟨hmax v, fun h => Nat.lt_of_le_of_lt (hπ v v₀ h) hv₀⟩
  rw [this]
  simp [f, Prod.Lex.toLex_le_toLex, hkey.eq_iff]

/-- **Expansion.** Lay out the vertices block by block, ordering the blocks by an injective
key and each block by its list. If at most `X` edges of the multigraph quotient cross each
prefix of the key, at most `X + d log₂ N + d` edges cross each frontier of the layout. -/
theorem exists_layout [Finite V] [Finite E] {key : c.blocks → ℕ}
    (hkey : key.Injective) {X : ℝ}
    (hX : ∀ q, ((c.multiQuotient.cut {B | key B < q}).ncard : ℝ) ≤ X) :
    ∃ π : Layout V, ∀ t,
      ((G.cut (π.initial t)).ncard : ℝ) ≤ X + d * Nat.log 2 (Nat.card V) + d := by
  classical
  obtain ⟨π, hπ⟩ := c.exists_layout_prefixes hkey
  refine ⟨π, fun t => ?_⟩
  have hX₀ : 0 ≤ X := (Nat.cast_nonneg _).trans (hX 0)
  rcases hπ t with h | ⟨B, r, hL⟩
  · rw [h, cut_empty, ncard_empty, Nat.cast_zero]
    positivity
  have hnat : (G.cut (π.initial t)).ncard ≤
      (c.multiQuotient.cut {B' | key B' < key B}).ncard +
        (d * Nat.log 2 (Nat.card V) + d) := by
    rw [hL]
    rw [← c.ncard_cut_multiQuotient]
    exact (ncard_le_ncard (G.cut_union_subset _ _)).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_left (c.ncard_cut_take_le B r) _))
  have hq := hX (key B)
  have hreal := Nat.cast_le (α := ℝ).mpr hnat
  push_cast at hreal
  linarith

end Compression

end Multigraph

end Proofs
