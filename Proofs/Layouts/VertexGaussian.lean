/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Gaussian.Basic

/-!
# Gaussian vertex scores

Give each vertex `v` its unit kernel row `x_v` (`Proofs.Layouts.Kernel`): the normalized
vector of distance weights `q ^ dist(v, z)`, truncated at radius `R`. Draw a standard Gaussian
vector `ω` and score each vertex by `⟨x_v, ω⟩` (`vertexScore`). Sorting the vertices by score
gives the layouts of `Proofs.Layouts.MultiGaussian`.

**One edge.** A threshold `t` crosses the edge `uv` when it separates the scores of `u` and `v`.
For maximum degree `d`, the truncated kernel gives the explicit correlation lower bound
`2q/(1+q²) - d((d-1)q²)^R`. If `ρ > -1` is no larger than that bound, Sheppard's bound says
that the edge crosses `t` with probability at most `arccos ρ / π`
(`measureReal_crossingEvent_le`).

**Locality.** A score depends only on the coordinates of `ω` in a ball of radius `R`
(`dependsOn_vertexEvent`, `dependsOn_crossingEvent`), and boundedly many such balls meet a given
one (`ball_overlap_le`). This is what the second-moment bound of `Proofs.Layouts.SecondMoment`
needs.

**The limit.** As `q` increases to `1/√(d - 1)` and `R` grows, the adjacent correlation in
maximum degree `d` tends to `2 √(d - 1) / d` (`vertexCorrelation`,
`exists_decay_radius_degree`), the neighbour correlation of Gaussian waves on the `d`-regular
tree. So the per-edge crossing probability tends to
`vertexCoefficient d = arccos (2 √(d - 1) / d) / π`.
-/

@[expose] public section

namespace Proofs.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-! ### Vertex scores and crossing events -/

section Scores

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The Gaussian score `⟨x_v, ω⟩` of a vertex: the inner product of its unit kernel row with
the sample. -/
noncomputable def vertexScore (q : ℝ) (R : ℕ) (ω : W → ℝ) (v : W) : ℝ :=
  form (unitKernel H q R v) ω

/-- The event that the score of `v` satisfies `p`. -/
def vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) : Set (W → ℝ) :=
  {ω | p (vertexScore H q R ω v)}

/-- The event that the threshold `t` separates the scores of the ends of an edge. -/
def crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) : Sym2 W → Set (W → ℝ) :=
  Sym2.lift ⟨fun u v => {ω | Between t (vertexScore H q R ω u) (vertexScore H q R ω v)},
    fun _ _ => by ext ω; simp only [Set.mem_ofPred_eq, Between, or_comm]⟩

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_vertexEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (v : W) : MeasurableSet (vertexEvent H q R p v) :=
  measurable_form _ hp

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    MeasurableSet (crossingEvent H q R t e) := by
  induction e using Sym2.ind with
  | _ u v => exact measurableSet_between (measurable_form _) (measurable_form _) t

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem vertexScore_congr (q : ℝ) (R : ℕ) (v : W) {ω ω' : W → ℝ}
    (h : ∀ z ∈ ball H v R, ω z = ω' z) : vertexScore H q R ω v = vertexScore H q R ω' v :=
  form_congr (fun _z hz => unitKernel_eq_zero_of_notMem_ball H hz) h

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem dependsOn_vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) :
    DependsOn (· ∈ vertexEvent H q R p v) (ball H v R : Set W) := by
  intro ω ω' h
  simp only [vertexEvent, Set.mem_ofPred_eq]
  rw [vertexScore_congr H q R v h]

omit [DecidableRel H.Adj] in
theorem dependsOn_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    DependsOn (· ∈ crossingEvent H q R t e) (edgeSupport H R e : Set W) := by
  induction e using Sym2.ind with
  | _ u v =>
  intro ω ω' h
  change (Between t (vertexScore H q R ω u) (vertexScore H q R ω v)) =
    (Between t (vertexScore H q R ω' u) (vertexScore H q R ω' v))
  rw [vertexScore_congr H q R u (fun z hz => h z (mem_union.mpr (Or.inl hz))),
    vertexScore_congr H q R v (fun z hz => h z (mem_union.mpr (Or.inr hz)))]

omit [DecidableEq W] in
/-- **One edge.** In maximum degree `d ≥ 2`, let `q ≥ 0` and let `ρ > -1` be no larger than
the explicit truncated-kernel lower bound
`2q/(1+q²) - d((d-1)q²)^R`. A threshold crosses an edge with probability at most
`arccos ρ / π`. -/
theorem measureReal_crossingEvent_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    {q : ℝ} (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ} (hρ0 : -1 < ρ)
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R)
    (t : ℝ) {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    (gaussPi W).real (crossingEvent H q R t e) ≤ Real.arccos ρ / Real.pi := by
  induction e using Sym2.ind with
  | _ u v =>
  have hcorr := hρ.trans (sum_unitKernel_mul_ge_degree H hd degree hq R
    (SimpleGraph.mem_edgeFinset.mp he))
  exact (gaussPi_between_le_arccos (sum_unitKernel_sq H q R u) (sum_unitKernel_sq H q R v)
    (hρ0.trans_le hcorr) t).trans (div_le_div_of_nonneg_right
      (Real.arccos_le_arccos hcorr) Real.pi_pos.le)

/-- The per-edge crossing coefficient of Gaussian vertex scores in maximum degree `d`:
`arccos (2 √(d - 1) / d) / π`. -/
noncomputable def vertexCoefficient (d : ℕ) : ℝ := Real.arccos (vertexCorrelation d) / Real.pi

end Scores

end Proofs.Gaussian
