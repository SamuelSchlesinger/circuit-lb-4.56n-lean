/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Gaussian.Basic

/-!
# Gaussian edge scores and their locality

Normalize the sum of the kernel rows at an edge. Its score depends only on the balls around
its endpoints, so the number of overlapping score supports is bounded by the degree and radius.
-/

@[expose] public section

namespace Proofs.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-! ### Edge vectors and scores -/

section Vectors

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The squared norm of the sum of two unit kernel rows. -/
noncomputable def pairNormSq (q : ℝ) (R : ℕ) (u v : W) : ℝ :=
  ∑ z, (unitKernel H q R u z + unitKernel H q R v z) ^ 2

theorem pairNormSq_comm (q : ℝ) (R : ℕ) (u v : W) :
    pairNormSq H q R u v = pairNormSq H q R v u := by
  simp only [pairNormSq, add_comm]

theorem pairNormSq_eq (q : ℝ) (R : ℕ) (u v : W) :
    pairNormSq H q R u v = 2 + 2 * ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  have hu := sum_unitKernel_sq H q R u
  have hv := sum_unitKernel_sq H q R v
  have : ∀ z, (unitKernel H q R u z + unitKernel H q R v z) ^ 2 =
      unitKernel H q R u z ^ 2 + unitKernel H q R v z ^ 2 +
        2 * (unitKernel H q R u z * unitKernel H q R v z) := fun z => by ring
  simp only [pairNormSq, this, sum_add_distrib, ← mul_sum, hu, hv]
  ring

/-- The unit vector of an edge: the normalized sum of the kernel rows of its endpoints. -/
noncomputable def edgeVector (q : ℝ) (R : ℕ) : Sym2 W → W → ℝ :=
  Sym2.lift ⟨fun u v z => (unitKernel H q R u z + unitKernel H q R v z) /
      Real.sqrt (pairNormSq H q R u v), fun u v => by
    funext z
    dsimp only
    rw [add_comm, pairNormSq_comm]⟩

@[simp] theorem edgeVector_mk (q : ℝ) (R : ℕ) (u v z : W) :
    edgeVector H q R s(u, v) z = (unitKernel H q R u z + unitKernel H q R v z) /
      Real.sqrt (pairNormSq H q R u v) := rfl

/-- The Gaussian score of an edge at the sample `ω`. -/
noncomputable def edgeScore (q : ℝ) (R : ℕ) (ω : W → ℝ) (e : Sym2 W) : ℝ :=
  form (edgeVector H q R e) ω

theorem measurable_edgeScore (q : ℝ) (R : ℕ) (e : Sym2 W) :
    Measurable fun ω => edgeScore H q R ω e :=
  measurable_form _

variable {H}

theorem sum_edgeVector_sq {q : ℝ} {R : ℕ} {u v : W} (hpos : 0 < pairNormSq H q R u v) :
    ∑ z, edgeVector H q R s(u, v) z ^ 2 = 1 := by
  simp only [edgeVector_mk, div_pow, ← sum_div]
  rw [Real.sq_sqrt hpos.le]
  exact div_self hpos.ne'

/-- The inner product of an edge vector with the row of an endpoint is `√((1 + ρ)/2)`, where
`ρ` is the correlation of the two endpoint rows. -/
theorem sum_edgeVector_mul {q : ℝ} {R : ℕ} {u v : W} (hpos : 0 < pairNormSq H q R u v) :
    ∑ z, edgeVector H q R s(u, v) z * unitKernel H q R v z =
      Real.sqrt ((1 + ∑ z, unitKernel H q R u z * unitKernel H q R v z) / 2) := by
  set ρ := ∑ z, unitKernel H q R u z * unitKernel H q R v z
  have hsq : pairNormSq H q R u v = 2 * (1 + ρ) := by rw [pairNormSq_eq]; ring
  have hpos' : 0 < 1 + ρ := by linarith
  have hnum : ∑ z, (unitKernel H q R u z + unitKernel H q R v z) * unitKernel H q R v z =
      1 + ρ := by
    have hv := sum_unitKernel_sq H q R v
    simp only [add_mul, sum_add_distrib, ← pow_two, hv]
    ring
  simp only [edgeVector_mk, div_mul_eq_mul_div, ← sum_div, hnum, hsq]
  rw [Real.sqrt_mul (by norm_num), show Real.sqrt ((1 + ρ) / 2) =
      Real.sqrt (1 + ρ) / Real.sqrt 2 from Real.sqrt_div' _ (by norm_num)]
  have h1 : 0 < Real.sqrt (1 + ρ) := Real.sqrt_pos.mpr hpos'
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  rw [Real.sq_sqrt hpos'.le]

end Vectors

/-! ### Locality -/

section Locality

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)

variable {H}

theorem edgeScore_congr {q : ℝ} {R : ℕ} {e : Sym2 W} {S : Finset W}
    (hS : edgeSupport H R e ⊆ S) {ω ω' : W → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    edgeScore H q R ω e = edgeScore H q R ω' e := by
  refine form_congr (S := S) (fun z hz => ?_) h
  induction e using Sym2.ind with
  | _ u v =>
    have hz' : z ∉ edgeSupport H R s(u, v) := fun h => hz (hS h)
    rw [edgeSupport_mk, mem_union, not_or] at hz'
    rw [edgeVector_mk, unitKernel_eq_zero_of_notMem_ball H hz'.1,
      unitKernel_eq_zero_of_notMem_ball H hz'.2, add_zero, zero_div]

variable [DecidableRel H.Adj]

/-- The supports of the edges at `v` lie in the ball of radius `R + 1` around `v`. -/
theorem edgeSupport_subset_ball {R : ℕ} {v : W} {e : Sym2 W} (he : e ∈ H.incidenceFinset v) :
    edgeSupport H R e ⊆ ball H v (R + 1) := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_sep_iff] at he
  obtain ⟨hedge, hv⟩ := he
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
  rw [edgeSupport_mk]
  exact union_subset (ball_mono H v (Nat.le_succ R))
    (ball_subset_ball_of_adj H ((SimpleGraph.mem_edgeSet H).mp hedge) R)

/-- At most `d |S|` edges have an endpoint in `S`. -/
theorem card_incidence_biUnion_le {d : ℕ} (degree : ∀ v, H.degree v ≤ d) (S : Finset W) :
    #(S.biUnion fun v => H.incidenceFinset v) ≤ d * #S := by
  calc _ ≤ ∑ v ∈ S, #(H.incidenceFinset v) := card_biUnion_le
    _ ≤ ∑ _v ∈ S, d := sum_le_sum fun v _ => by
      rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact degree v
    _ = d * #S := by simp [Nat.mul_comm]

variable (H) in
/-- Boundedly many edge supports meet that of a given edge. -/
theorem edge_overlap_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d) (R : ℕ)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    #{l ∈ H.edgeFinset | ¬ Disjoint (edgeSupport H R e) (edgeSupport H R l)} ≤
      vertexOverlap d R := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  have hsupp : edgeSupport H R s(u, v) ⊆ ball H u (R + 1) := by
    rw [edgeSupport_mk]
    exact union_subset (ball_mono H u (Nat.le_succ R)) (ball_subset_ball_of_adj H huv R)
  have hsub : {l ∈ H.edgeFinset | ¬ Disjoint (edgeSupport H R s(u, v)) (edgeSupport H R l)} ⊆
      (ball H u (2 * R + 1)).biUnion (fun c => H.incidenceFinset c) := by
    intro l hl
    obtain ⟨hlE, hdisj⟩ := mem_filter.mp hl
    induction l using Sym2.ind with
    | _ a b =>
    have hab : H.Adj a b := SimpleGraph.mem_edgeFinset.mp hlE
    obtain ⟨z, hz₁, hz₂⟩ := not_disjoint_iff.mp hdisj
    have near (c : W) (hc : z ∈ ball H c R) : c ∈ ball H u (2 * R + 1) := by
      have := mem_ball_of_not_disjoint H
        (not_disjoint_iff.mpr ⟨z, hsupp hz₁, hc⟩)
      rwa [show R + 1 + R = 2 * R + 1 by ring] at this
    rw [edgeSupport_mk, mem_union] at hz₂
    rcases hz₂ with hza | hzb
    · exact mem_biUnion.mpr ⟨a, near a hza, SimpleGraph.mem_incidenceFinset.mpr
        ⟨(SimpleGraph.mem_edgeSet H).mpr hab, by simp⟩⟩
    · exact mem_biUnion.mpr ⟨b, near b hzb, SimpleGraph.mem_incidenceFinset.mpr
        ⟨(SimpleGraph.mem_edgeSet H).mpr hab, by simp⟩⟩
  calc _ ≤ #((ball H u (2 * R + 1)).biUnion fun c => H.incidenceFinset c) := card_le_card hsub
    _ ≤ d * #(ball H u (2 * R + 1)) := card_incidence_biUnion_le degree _
    _ ≤ d * d ^ (2 * R + 1 + 1) := Nat.mul_le_mul_left d
        (card_ball_le_degree H hd degree u _)
    _ = vertexOverlap d R := by unfold vertexOverlap; rw [← pow_succ']

end Locality

end Proofs.Gaussian
