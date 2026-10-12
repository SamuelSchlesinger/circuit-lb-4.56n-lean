/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Rectangle
public import Proofs.ForMathlib.SetCard
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Read-once branching programs and the rectangle bound

A *layered read-once nondeterministic branching program* reads the coordinates of an input
`x : ι → U` a few at a time: `∅ = X 0 ⊆ X 1 ⊆ ... ⊆ X T = ι`. Its nodes at each layer are
*states*. An *edge* of step `t` joins a state at layer `t` to a state at layer `t + 1` and is
labelled by an assignment to the coordinates `X (t + 1) \ X t` read during the step. An input is
*accepted* when some path from the start state at layer `0` to the accepting state at layer `T`
follows edges whose labels agree with the input. Each coordinate is read at exactly one step.
The program is *unambiguous* when every input has at most one accepting path; the rectangle
bound below does not need this.

**Concatenation** (`IsAcceptingPath.splice`). If accepting paths for `x` and `y` are in the same
state at layer `t`, following the first up to layer `t` and the second afterwards is an
accepting path for the input that agrees with `x` on `X t` and with `y` elsewhere. So the inputs
whose paths pass through a fixed state at layer `t` span a rectangle, for the cut `X t`, inside
the accepted set.

**The rectangle bound** (`ncard_accepted_le_of_smallSides`). Suppose that at every layer, the
inputs whose paths share a state have fewer than `K` distinct parts on one side of the cut, as
when the accepted set `S` is `K`-rectangle-free (`ncard_accepted_le`). Then the program has at
least `|S| / (K - 1) ^ 2` edges.

Fix an accepting path for every accepted input. The proof charges each input `x` to the first
layer `t + 1` at which the inputs whose paths share its state have at least `K` distinct parts on
`X (t + 1)`. Their rectangular hull lies inside `S`, so they have fewer than `K` distinct parts
off `X (t + 1)`. At layer `t` the inputs sharing the state of `x` still had fewer than `K`
distinct parts on `X t`. An input charged to step `t` is determined by the edge its path takes
at that step, its part on `X t`, and its part off `X (t + 1)`; hence at most `(K - 1) ^ 2`
inputs are charged to each edge.

**Peeling** (`abs_signedCount_accepted_le`). In an unambiguous program the inputs whose paths
pass through a state are exactly a rectangle, and deleting the state removes exactly them,
leaving an unambiguous program. So while some state has at least `K` distinct parts on both
sides of its cut, its rectangle can be peeled off; what remains has small sides and is counted
by the rectangle bound. If `S` has bias at most `b` on rectangles with both sides of size at
least `K`, the accepted inputs in `S` and those outside it then differ in number by at most
`2 b |accepted| + (K - 1) ^ 2 · size`. The peeling argument is due to Sam McGuire.

Constraint networks laid out along a vertex ordering give such programs, whose states are the
values on the edges of a frontier (`Proofs.Network.branchingProgram`).

## Main definitions

* `Proofs.ReadOnceNBP ι U M`: a layered read-once nondeterministic branching program with
  states in `M`.
* `Proofs.ReadOnceNBP.accepted`: its accepted inputs.
* `Proofs.ReadOnceNBP.Unambiguous`: every input has at most one accepting path.
* `Proofs.ReadOnceNBP.size`: its number of edges.

## Main results

* `Proofs.ReadOnceNBP.IsAcceptingPath.splice`: concatenation of accepting paths.
* `Proofs.ReadOnceNBP.ncard_accepted_le_of_smallSides`, `Proofs.ReadOnceNBP.ncard_accepted_le`:
  the rectangle bound.
* `Proofs.ReadOnceNBP.abs_signedCount_accepted_le`: peeling.
-/

@[expose] public section

namespace Proofs

open Set

variable {ι U M : Type*}

/-- A *layered read-once nondeterministic branching program* over inputs `ι → U`, with states
in `M`. Step `t` reads the coordinates in `revealed (t + 1) \ revealed t`. -/
structure ReadOnceNBP (ι U M : Type*) where
  /-- The number of steps. -/
  length : ℕ
  /-- The coordinates read before layer `t`. -/
  revealed : ℕ → Set ι
  /-- Nothing is read before the first layer. -/
  revealed_zero : revealed 0 = ∅
  /-- Everything is read before the last layer. -/
  revealed_length : revealed length = univ
  /-- A coordinate once read stays read. -/
  revealed_mono : Monotone revealed
  /-- The start state, at layer `0`. -/
  start : M
  /-- The accepting state, at the last layer. -/
  accept : M
  /-- `Edge t m a m'`: an edge of step `t` joins the state `m` at layer `t` to the state `m'` at
  layer `t + 1`, labelled by the values `a` of the coordinates read during the step. -/
  Edge : (t : ℕ) → M → (↥(revealed (t + 1) \ revealed t) → U) → M → Prop

namespace ReadOnceNBP

variable (P : ReadOnceNBP ι U M)

/-- The coordinates read during step `t`, between layers `t` and `t + 1`. -/
abbrev newly (t : ℕ) : Set ι :=
  P.revealed (t + 1) \ P.revealed t

/-- `γ` is an *accepting path* for the input `x`: it starts at the start state, ends at the
accepting state, and at each step follows an edge labelled by the values of `x`. -/
structure IsAcceptingPath (x : ι → U) (γ : ℕ → M) : Prop where
  /-- The path starts at the start state. -/
  start : γ 0 = P.start
  /-- The path ends at the accepting state. -/
  accept : γ P.length = P.accept
  /-- Each step follows an edge labelled by the values of `x`. -/
  edge : ∀ t < P.length, P.Edge t (γ t) ((P.newly t).domRestrict x) (γ (t + 1))

/-- The *accepted* inputs: those with an accepting path. -/
def accepted : Set (ι → U) :=
  {x | ∃ γ, P.IsAcceptingPath x γ}

/-- The program is *unambiguous* when every input has at most one accepting path: two accepting
paths for the same input agree up to the last layer. -/
def Unambiguous : Prop :=
  ∀ x γ δ, P.IsAcceptingPath x γ → P.IsAcceptingPath x δ → ∀ t ≤ P.length, γ t = δ t

/-- The edges of step `t`, each given by its source state, its label, and its target state. -/
def edges (t : ℕ) : Set (M × (P.newly t → U) × M) :=
  {e | P.Edge t e.1 e.2.1 e.2.2}

/-- The *size* of the program: its number of edges. -/
noncomputable def size : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.edges t).ncard

/-- A coordinate read at step `s < t` was read before layer `t`. -/
theorem newly_subset_revealed {s t : ℕ} (h : s < t) : P.newly s ⊆ P.revealed t :=
  fun _ hi => P.revealed_mono (Nat.succ_le_of_lt h) hi.1

/-- A coordinate read at step `s ≥ t` was not read before layer `t`. -/
theorem newly_subset_compl {s t : ℕ} (h : t ≤ s) : P.newly s ⊆ (P.revealed t)ᶜ :=
  fun _ hi hit => hi.2 (P.revealed_mono h hit)

variable {P}

/-- **Concatenation.** Let the accepting paths `γ` for `x` and `δ` for `y` be in the same state
at layer `t`. Following `γ` up to layer `t` and `δ` afterwards is an accepting path for any
input that agrees with `x` on the coordinates read before layer `t` and with `y` on the
others. -/
theorem IsAcceptingPath.splice {x y z : ι → U} {γ δ : ℕ → M} (hγ : P.IsAcceptingPath x γ)
    (hδ : P.IsAcceptingPath y δ) {t : ℕ} (ht : γ t = δ t) (hzx : EqOn z x (P.revealed t))
    (hzy : EqOn z y (P.revealed t)ᶜ) :
    P.IsAcceptingPath z fun s => if s ≤ t then γ s else δ s := by
  refine ⟨by simpa using hγ.start, ?_, fun s hs => ?_⟩
  · split_ifs
    · exact hγ.accept
    · exact hδ.accept
  rcases lt_or_ge s t with hst | hts
  · have hz : (P.newly s).domRestrict z = (P.newly s).domRestrict x :=
      funext fun i => hzx (P.newly_subset_revealed hst i.2)
    rw [ite_eq_left hst.le, ite_eq_left (Nat.succ_le_of_lt hst), hz]
    exact hγ.edge s hs
  · have hz : (P.newly s).domRestrict z = (P.newly s).domRestrict y :=
      funext fun i => hzy (P.newly_subset_compl hts i.2)
    have hδs : (if s ≤ t then γ s else δ s) = δ s := by
      split_ifs with h
      · rw [le_antisymm h hts, ht]
      · rfl
    rw [hδs, ite_eq_right (by lia), hz]
    exact hδ.edge s hs

variable (P)

open Classical in
/-- An accepting path for each accepted input, chosen once and for all. -/
noncomputable def path (x : ι → U) : ℕ → M :=
  if h : ∃ γ, P.IsAcceptingPath x γ then h.choose else fun _ => P.start

/-- The chosen path of an accepted input is an accepting path. -/
theorem isAcceptingPath_path {x : ι → U} (hx : x ∈ P.accepted) :
    P.IsAcceptingPath x (P.path x) := by
  unfold path
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hx h

/-- The edge that the chosen path of `x` takes at step `t`. -/
noncomputable def edgeOf (t : ℕ) (x : ι → U) : M × (P.newly t → U) × M :=
  (P.path x t, (P.newly t).domRestrict x, P.path x (t + 1))

/-- The chosen path of an accepted input follows edges of the program. -/
theorem edgeOf_mem_edges {x : ι → U} (hx : x ∈ P.accepted) {t : ℕ} (ht : t < P.length) :
    P.edgeOf t x ∈ P.edges t :=
  (P.isAcceptingPath_path hx).edge t ht

/-! ### The proof of the rectangle bound -/

/-- The *peers* of `x` at layer `t`: the accepted inputs whose chosen paths are in the same state
as that of `x`. -/
def peers (t : ℕ) (x : ι → U) : Set (ι → U) :=
  {y ∈ P.accepted | P.path y t = P.path x t}

/-- The distinct parts on the coordinates read before layer `t` among the peers of `x`. -/
def pastSide (t : ℕ) (x : ι → U) : Set (P.revealed t → U) :=
  (P.revealed t).domRestrict '' P.peers t x

/-- The distinct parts on the coordinates not read before layer `t` among the peers of `x`. -/
def futureSide (t : ℕ) (x : ι → U) : Set (↥(P.revealed t)ᶜ → U) :=
  (P.revealed t)ᶜ.domRestrict '' P.peers t x

/-- The rectangular hull of the peers lies inside the accepted set: one of its sides is small. -/
theorem pastSide_lt_or_futureSide_lt [Finite ι] [Finite U] {K : ℕ}
    (hS : RectangleFree P.accepted K) (t : ℕ) (x : ι → U) :
    (P.pastSide t x).ncard < K ∨ (P.futureSide t x).ncard < K := by
  refine hS.ncard_lt_or _ _ _ fun z ⟨⟨y, ⟨hy, hyx⟩, hzy⟩, ⟨y', ⟨hy', hy'x⟩, hzy'⟩⟩ => ?_
  exact ⟨_, (P.isAcceptingPath_path hy).splice (P.isAcceptingPath_path hy')
    (hyx.trans hy'x.symm) (domRestrict_eq_domRestrict_iff.mp hzy).symm
    (domRestrict_eq_domRestrict_iff.mp hzy').symm⟩

/-- At every layer, the inputs sharing the state of an accepted input have fewer than `K`
distinct parts on one side of the cut. -/
def SmallSides (K : ℕ) : Prop :=
  ∀ t ≤ P.length, ∀ x ∈ P.accepted, (P.pastSide t x).ncard < K ∨ (P.futureSide t x).ncard < K

/-- A rectangle-free accepted set has small sides. -/
theorem smallSides_of_rectangleFree [Finite ι] [Finite U] {K : ℕ}
    (hS : RectangleFree P.accepted K) : P.SmallSides K :=
  fun t _ x _ => P.pastSide_lt_or_futureSide_lt hS t x

/-- An accepted input is among its own peers, so both of its sides are nonempty. -/
theorem one_le_ncard_pastSide [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ P.accepted) (t : ℕ) :
    1 ≤ (P.pastSide t x).ncard :=
  (ncard_pos (toFinite _)).mpr ⟨_, x, ⟨hx, rfl⟩, rfl⟩

theorem one_le_ncard_futureSide [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ P.accepted)
    (t : ℕ) : 1 ≤ (P.futureSide t x).ncard :=
  (ncard_pos (toFinite _)).mpr ⟨_, x, ⟨hx, rfl⟩, rfl⟩

variable {P} in
/-- Small sides force `K > 1` once some input is accepted. -/
theorem SmallSides.one_lt [Finite ι] [Finite U] {K : ℕ} (hS : P.SmallSides K)
    (hne : P.accepted.Nonempty) : 1 < K := by
  obtain ⟨x, hx⟩ := hne
  rcases hS 0 (Nat.zero_le _) x hx with h | h
  · exact (P.one_le_ncard_pastSide hx 0).trans_lt h
  · exact (P.one_le_ncard_futureSide hx 0).trans_lt h

/-- A program that accepts some input and has a step has an edge. -/
theorem one_le_size [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length)
    (hne : P.accepted.Nonempty) : 1 ≤ P.size := by
  obtain ⟨x, hx⟩ := hne
  have h0 : 1 ≤ (P.edges 0).ncard := (ncard_pos (toFinite _)).mpr ⟨_, P.edgeOf_mem_edges hx hL⟩
  exact h0.trans (Finset.single_le_sum (f := fun t => (P.edges t).ncard)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hL))

/-- At the first layer nothing has been read, so there is at most one part. -/
theorem ncard_pastSide_zero_le (x : ι → U) : (P.pastSide 0 x).ncard ≤ 1 := by
  have : Subsingleton (P.revealed 0 → U) :=
    ⟨fun a b => funext fun i => absurd i.2 (by simp [P.revealed_zero])⟩
  exact (ncard_le_one (toFinite _)).mpr fun a _ b _ => Subsingleton.elim a b

/-- At the last layer everything has been read and every accepted input is a peer, so the parts
are as numerous as the accepted inputs. -/
theorem ncard_pastSide_length {x : ι → U} (hx : x ∈ P.accepted) :
    (P.pastSide P.length x).ncard = P.accepted.ncard := by
  have hpeers : P.peers P.length x = P.accepted :=
    subset_antisymm (fun _ hy => hy.1) fun y hy =>
      ⟨hy, (P.isAcceptingPath_path hy).accept.trans (P.isAcceptingPath_path hx).accept.symm⟩
  rw [pastSide, hpeers]
  refine ncard_image_of_injective _ fun y y' h => funext fun i => ?_
  exact domRestrict_eq_domRestrict_iff.mp h (by simp [P.revealed_length])

/-- The time at which `x` is charged: the first layer at which its peers have at least `K`
distinct parts. -/
private noncomputable def chargeTime (K : ℕ) (x : ι → U) : ℕ :=
  sInf {t | K ≤ (P.pastSide t x).ncard}

/-- The accepted inputs charged to step `t`: those whose peers first have `K` distinct parts at
layer `t + 1`. -/
private def chargedInputs (K t : ℕ) : Set (ι → U) :=
  {x ∈ P.accepted | P.chargeTime K x = t + 1}

/-- The edges to which some input is charged, summed over the steps. -/
private noncomputable def chargedEdgeCount (K : ℕ) : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.edgeOf t '' P.chargedInputs K t).ncard

/-- The charged edges are among the edges of the program. -/
private theorem chargedEdgeCount_le [Finite ι] [Finite U] [Finite M] (K : ℕ) :
    P.chargedEdgeCount K ≤ P.size :=
  Finset.sum_le_sum fun _ ht => ncard_le_ncard
    (image_subset_iff.mpr fun _ hx => P.edgeOf_mem_edges hx.1 (Finset.mem_range.mp ht))
    (toFinite _)

/-- At the last layer the peers of an accepted input have `|accepted| ≥ K` distinct parts. -/
private theorem mem_chargeSet_length {K : ℕ} (hK : K ≤ P.accepted.ncard) {x : ι → U}
    (hx : x ∈ P.accepted) : P.length ∈ {t | K ≤ (P.pastSide t x).ncard} :=
  show K ≤ _ by rw [P.ncard_pastSide_length hx]; exact hK

/-- An accepted input is charged by the last layer. -/
private theorem chargeTime_le_length {K : ℕ} (hK : K ≤ P.accepted.ncard) {x : ι → U}
    (hx : x ∈ P.accepted) : P.chargeTime K x ≤ P.length :=
  Nat.sInf_le (P.mem_chargeSet_length hK hx)

/-- At its charge time, the peers of an accepted input have at least `K` distinct parts. -/
private theorem le_ncard_pastSide_chargeTime {K : ℕ} (hK : K ≤ P.accepted.ncard) {x : ι → U}
    (hx : x ∈ P.accepted) : K ≤ (P.pastSide (P.chargeTime K x) x).ncard :=
  Nat.sInf_mem ⟨_, P.mem_chargeSet_length hK hx⟩

/-- Before its charge time, the peers of an input have fewer than `K` distinct parts. -/
private theorem ncard_pastSide_lt_of_lt_chargeTime {K t : ℕ} {x : ι → U}
    (ht : t < P.chargeTime K x) : (P.pastSide t x).ncard < K :=
  not_le.mp (Nat.notMem_of_lt_sInf (s := {t | K ≤ (P.pastSide t x).ncard}) ht)

/-- For `K > 1` no accepted input is charged at the first layer, where its peers have at most
one part. -/
private theorem chargeTime_pos {K : ℕ} (hK1 : 1 < K) (hK : K ≤ P.accepted.ncard) {x : ι → U}
    (hx : x ∈ P.accepted) : 0 < P.chargeTime K x := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have h := P.le_ncard_pastSide_chargeTime hK hx
  rw [h0] at h
  have := P.ncard_pastSide_zero_le x
  lia

/-- **One edge.** At most `(K - 1) ^ 2` inputs charged to step `t` take a given edge. Such an
input is determined by the edge, its part on the coordinates read before layer `t`, of which its
peers have fewer than `K`, and its part off the coordinates read before layer `t + 1`, of which
its peers there have fewer than `K` because their parts on the read coordinates do not. -/
private theorem ncard_chargedInputs_inter_le [Finite ι] [Finite U] {K : ℕ}
    (hS : P.SmallSides K) (hK : K ≤ P.accepted.ncard) (t : ℕ)
    (τ : M × (P.newly t → U) × M) :
    (P.chargedInputs K t ∩ P.edgeOf t ⁻¹' {τ}).ncard ≤ (K - 1) ^ 2 := by
  rcases (P.chargedInputs K t ∩ P.edgeOf t ⁻¹' {τ}).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  obtain ⟨⟨hxS, hxcharge⟩, hxτ⟩ := hx
  have hpast : (P.pastSide t x).ncard ≤ K - 1 := by
    have := P.ncard_pastSide_lt_of_lt_chargeTime (K := K) (t := t) (x := x) (by lia)
    lia
  have hfuture : (P.futureSide (t + 1) x).ncard ≤ K - 1 := by
    have := P.le_ncard_pastSide_chargeTime hK hxS
    rw [hxcharge] at this
    rcases hS (t + 1) (hxcharge ▸ P.chargeTime_le_length hK hxS) x hxS with h | h <;> lia
  calc (P.chargedInputs K t ∩ P.edgeOf t ⁻¹' {τ}).ncard
      ≤ (P.pastSide t x ×ˢ P.futureSide (t + 1) x).ncard := by
        refine ncard_le_ncard_of_injOn
          (fun y => ((P.revealed t).domRestrict y, (P.revealed (t + 1))ᶜ.domRestrict y))
          ?_ ?_ (toFinite _)
        · rintro y ⟨⟨hyS, -⟩, hyτ⟩
          have hyx : P.edgeOf t y = P.edgeOf t x := hyτ.trans hxτ.symm
          simp only [edgeOf, Prod.mk.injEq] at hyx
          exact ⟨⟨y, ⟨hyS, hyx.1⟩, rfl⟩, ⟨y, ⟨hyS, hyx.2.2⟩, rfl⟩⟩
        · rintro y ⟨⟨-, -⟩, hyτ⟩ y' ⟨⟨-, -⟩, hy'τ⟩ hyy'
          simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hyy'
          have h := hyτ.trans hy'τ.symm
          simp only [edgeOf, Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h
          funext i
          grind [Set.EqOn]
    _ = (P.pastSide t x).ncard * (P.futureSide (t + 1) x).ncard := ncard_prod
    _ ≤ (K - 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul hpast hfuture

/-- **Charging.** If the accepted set has small sides and at least `K` elements, every
accepted input is charged to some step, so by the bound for one edge, the accepted set has at
most `(K - 1) ^ 2` times as many elements as there are charged edges. -/
private theorem ncard_le_charged [Finite ι] [Finite U] {K : ℕ}
    (hS : P.SmallSides K) (hK : K ≤ P.accepted.ncard) :
    P.accepted.ncard ≤ (K - 1) ^ 2 * P.chargedEdgeCount K := by
  rcases P.accepted.eq_empty_or_nonempty with h | hne
  · simp [h]
  have hpos : ∀ x ∈ P.accepted, 0 < P.chargeTime K x :=
    fun x hx => P.chargeTime_pos (hS.one_lt hne) hK hx
  -- Split the accepted set by the step `t` whose completion charges an input.
  let step : (ι → U) → ℕ := fun x => P.chargeTime K x - 1
  have hstep (t : ℕ) : P.accepted ∩ step ⁻¹' {t} = P.chargedInputs K t := by
    ext x
    change (x ∈ P.accepted ∧ P.chargeTime K x - 1 = t) ↔
      x ∈ P.accepted ∧ P.chargeTime K x = t + 1
    grind
  calc P.accepted.ncard
      ≤ ∑ t ∈ Finset.range P.length, (P.accepted ∩ step ⁻¹' {t}).ncard :=
        ncard_le_sum_ncard_fiber (toFinite _) step P.length fun x hx => by
          have := P.chargeTime_le_length hK hx; have := hpos x hx; simp only [step]; lia
    _ ≤ ∑ t ∈ Finset.range P.length, (K - 1) ^ 2 *
        (P.edgeOf t '' P.chargedInputs K t).ncard := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [hstep t]
        exact ncard_le_mul_ncard_image (toFinite _) (P.edgeOf t) _
          (P.ncard_chargedInputs_inter_le hS hK t)
    _ = (K - 1) ^ 2 * P.chargedEdgeCount K := (Finset.mul_sum ..).symm

/-- **The rectangle bound.** If at every layer the inputs sharing the state of an accepted
input have fewer than `K` distinct parts on one side of the cut, the program has at least
`|accepted| / (K - 1) ^ 2` edges. -/
theorem ncard_accepted_le_of_smallSides [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length)
    {K : ℕ} (hS : P.SmallSides K) : P.accepted.ncard ≤ (K - 1) ^ 2 * P.size := by
  rcases P.accepted.eq_empty_or_nonempty with h | hne
  · simp [h]
  have hK1 := hS.one_lt hne
  by_cases hK : K ≤ P.accepted.ncard
  · exact (P.ncard_le_charged hS hK).trans (Nat.mul_le_mul_left _ (P.chargedEdgeCount_le K))
  · calc P.accepted.ncard ≤ K - 1 := by lia
      _ ≤ (K - 1) ^ 2 * 1 := by rw [sq, mul_one]; exact Nat.le_mul_of_pos_left _ (by lia)
      _ ≤ (K - 1) ^ 2 * P.size := Nat.mul_le_mul_left _ (P.one_le_size hL hne)

/-- **The rectangle bound for rectangle-free sets.** A read-once branching program whose
accepted set is `K`-rectangle-free has at least `|accepted| / (K - 1) ^ 2` edges. -/
theorem ncard_accepted_le [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length) {K : ℕ}
    (hS : RectangleFree P.accepted K) : P.accepted.ncard ≤ (K - 1) ^ 2 * P.size :=
  P.ncard_accepted_le_of_smallSides hL (P.smallSides_of_rectangleFree hS)

/-! ### Peeling large rectangles -/

/-- The program with the state `m` deleted from layer `t`: no edge enters or leaves it. -/
def eraseNode (t : ℕ) (m : M) : ReadOnceNBP ι U M :=
  { P with Edge := fun s m₁ a m₂ => P.Edge s m₁ a m₂ ∧ ¬(s = t ∧ m₁ = m) ∧ ¬(s + 1 = t ∧ m₂ = m) }

variable {P}

theorem IsAcceptingPath.of_eraseNode {t : ℕ} {m : M} {x : ι → U} {γ : ℕ → M}
    (h : (P.eraseNode t m).IsAcceptingPath x γ) : P.IsAcceptingPath x γ :=
  ⟨h.start, h.accept, fun s hs => (h.edge s hs).1⟩

/-- The accepting paths of the program with a state deleted are those avoiding it. -/
theorem isAcceptingPath_eraseNode_iff (hL : 0 < P.length) {t : ℕ} (ht : t ≤ P.length) {m : M}
    {x : ι → U} {γ : ℕ → M} :
    (P.eraseNode t m).IsAcceptingPath x γ ↔ P.IsAcceptingPath x γ ∧ γ t ≠ m := by
  constructor
  · intro h
    refine ⟨h.of_eraseNode, fun hγ => ?_⟩
    rcases ht.lt_or_eq with ht | ht
    · exact (h.edge t ht).2.1 ⟨rfl, hγ⟩
    · refine (h.edge (P.length - 1) (Nat.sub_lt hL one_pos)).2.2 ⟨by lia, ?_⟩
      rw [show P.length - 1 + 1 = t by lia]
      exact hγ
  · rintro ⟨h, hγ⟩
    refine ⟨h.start, h.accept, fun s hs => ⟨h.edge s hs, ?_, ?_⟩⟩
    · rintro ⟨rfl, hs'⟩
      exact hγ hs'
    · rintro ⟨rfl, hs'⟩
      exact hγ hs'

theorem Unambiguous.eraseNode (hP : P.Unambiguous) (t : ℕ) (m : M) :
    (P.eraseNode t m).Unambiguous :=
  fun x γ δ hγ hδ s hs => hP x γ δ hγ.of_eraseNode hδ.of_eraseNode s hs

/-- In an unambiguous program, deleting a state removes exactly the inputs whose paths pass
through it. -/
theorem accepted_eraseNode (hP : P.Unambiguous) (hL : 0 < P.length) {t : ℕ} (ht : t ≤ P.length)
    (m : M) : (P.eraseNode t m).accepted = {x ∈ P.accepted | P.path x t ≠ m} := by
  ext x
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨hγ', hγt⟩ := (isAcceptingPath_eraseNode_iff hL ht).mp hγ
    have hx : x ∈ P.accepted := ⟨γ, hγ'⟩
    exact ⟨hx, fun h => hγt ((hP x γ _ hγ' (P.isAcceptingPath_path hx) t ht).trans h)⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨_, (isAcceptingPath_eraseNode_iff hL ht).mpr ⟨P.isAcceptingPath_path hx, hxt⟩⟩

theorem size_eraseNode_le [Finite ι] [Finite U] [Finite M] (t : ℕ) (m : M) :
    (P.eraseNode t m).size ≤ P.size :=
  Finset.sum_le_sum fun _ _ => ncard_le_ncard (fun _ he => he.1) (toFinite _)

/-- In an unambiguous program, the inputs whose paths share a state are exactly the rectangle
spanned by their parts. -/
theorem Unambiguous.peers_eq_rectangle (hP : P.Unambiguous) {t : ℕ} (ht : t ≤ P.length)
    (x : ι → U) :
    P.peers t x = rectangle (P.revealed t) (P.pastSide t x) (P.futureSide t x) := by
  refine subset_antisymm (fun y hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩) ?_
  rintro z ⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
  have hγ := (P.isAcceptingPath_path ha.1).splice (P.isAcceptingPath_path hb.1)
    (ha.2.trans hb.2.symm) (domRestrict_eq_domRestrict_iff.mp haz).symm
    (domRestrict_eq_domRestrict_iff.mp hbz).symm
  have hz : z ∈ P.accepted := ⟨_, hγ⟩
  refine ⟨hz, ?_⟩
  rw [hP z _ _ (P.isAcceptingPath_path hz) hγ t ht]
  simpa using ha.2

variable (P)

/-- **Peeling.** Let `S` have bias at most `b ≥ 0` on rectangles with both sides of size at
least `K`. Then the accepted inputs of an unambiguous program that lie in `S` and those that do
not differ in number by at most `2 b |accepted| + (K - 1) ^ 2 · size`.

While the inputs sharing some state have at least `K` distinct parts on both sides of its cut,
they form such a rectangle, and deleting the state removes exactly them and leaves an
unambiguous program. When no such state is left, the rectangle bound counts the remaining
inputs. The argument is due to Sam McGuire. -/
theorem abs_signedCount_accepted_le [Finite ι] [Finite U] [Finite M] (hP : P.Unambiguous)
    (hL : 0 < P.length) {S : Set (ι → U)} {K : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hS : RectangleBias S K b) :
    |signedCount S P.accepted| ≤ 2 * b * P.accepted.ncard + ((K - 1) ^ 2 * P.size : ℕ) := by
  induction hn : P.accepted.ncard using Nat.strong_induction_on generalizing P with
  | h n ih =>
    subst hn
    by_cases hthick : ∃ t ≤ P.length, ∃ x ∈ P.accepted,
        K ≤ (P.pastSide t x).ncard ∧ K ≤ (P.futureSide t x).ncard
    · obtain ⟨t, ht, x, hx, hA, hB⟩ := hthick
      -- The peers of `x` form a large rectangle; delete their state.
      have hR : P.peers t x ⊆ P.accepted := fun _ hy => hy.1
      have hacc : (P.eraseNode t (P.path x t)).accepted = P.accepted \ P.peers t x := by
        rw [accepted_eraseNode hP hL ht]
        ext y
        simp only [peers, mem_ofPred_eq, mem_sdiff]
        tauto
      have hcard := ncard_sdiff_add_ncard_of_subset hR
      have hpos : 0 < (P.peers t x).ncard := (ncard_pos (toFinite _)).mpr ⟨x, hx, rfl⟩
      have hrest := ih _ (by rw [hacc]; lia) (P.eraseNode t (P.path x t))
        (hP.eraseNode _ _) hL rfl
      rw [hacc] at hrest
      have hrect : |signedCount S (P.peers t x)| ≤ 2 * b * (P.peers t x).ncard := by
        rw [hP.peers_eq_rectangle ht x]
        exact hS.abs_signedCount_rectangle_le hA hB
      have hsize : (((K - 1) ^ 2 * (P.eraseNode t (P.path x t)).size : ℕ) : ℝ) ≤
          ((K - 1) ^ 2 * P.size : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_left _ (P.size_eraseNode_le t (P.path x t))
      have hcardR : ((P.accepted \ P.peers t x).ncard : ℝ) + (P.peers t x).ncard =
          P.accepted.ncard := by exact_mod_cast hcard
      rw [signedCount_sdiff S hR]
      calc |signedCount S (P.peers t x) + signedCount S (P.accepted \ P.peers t x)|
          ≤ |signedCount S (P.peers t x)| + |signedCount S (P.accepted \ P.peers t x)| :=
            abs_add_le _ _
        _ ≤ 2 * b * P.accepted.ncard + ((K - 1) ^ 2 * P.size : ℕ) := by
            rw [← hcardR]
            linarith
    · push Not at hthick
      have hsmall : P.SmallSides K := fun t ht x hx => by
        by_cases hA : K ≤ (P.pastSide t x).ncard
        · exact Or.inr (hthick t ht x hx hA)
        · exact Or.inl (not_le.mp hA)
      have hcount : (P.accepted.ncard : ℝ) ≤ ((K - 1) ^ 2 * P.size : ℕ) := by
        exact_mod_cast P.ncard_accepted_le_of_smallSides hL hsmall
      linarith [abs_signedCount_le S P.accepted,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b) (Nat.cast_nonneg (α := ℝ) P.accepted.ncard)]

end ReadOnceNBP

end Proofs
