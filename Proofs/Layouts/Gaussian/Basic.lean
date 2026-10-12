/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Kernel
public import Proofs.Layouts.Probability

/-!
# Shared Gaussian layout estimates

Estimates shared by the vertex-score and edge-score layouts: the supports of the scores and how
many of them overlap, deviations of counts of events, and the limiting adjacent correlation of
the kernel rows.
-/

@[expose] public section

namespace Proofs.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-! ### Locality -/

section Locality

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)

/-- A form depends only on the coordinates where its coefficients are nonzero. -/
theorem form_congr {ι : Type} [Fintype ι] {α : ι → ℝ} {S : Finset ι}
    (hα : ∀ i ∉ S, α i = 0) {ω ω' : ι → ℝ} (h : ∀ i ∈ S, ω i = ω' i) :
    form α ω = form α ω' := by
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · rw [h i hi]
  · simp [hα i hi]

/-- The coordinates on which the score of an edge depends: the kernel balls of its endpoints. -/
noncomputable def edgeSupport (R : ℕ) : Sym2 W → Finset W :=
  Sym2.lift ⟨fun u v => ball H u R ∪ ball H v R, fun _ _ => union_comm _ _⟩

@[simp] theorem edgeSupport_mk (R : ℕ) (u v : W) :
    edgeSupport H R s(u, v) = ball H u R ∪ ball H v R := rfl

variable {H}

variable [DecidableRel H.Adj]

/-- The number of kernel supports of radius `R` that may meet a given one, in maximum degree
`d`: one bound serves vertex events and edge events alike. -/
def vertexOverlap (d R : ℕ) : ℕ := d ^ (2 * R + 3)

variable (H) in
/-- Boundedly many balls of radius `R` meet a given one. -/
theorem ball_overlap_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d) (R : ℕ) (v : W) :
    #{w | ¬ Disjoint (ball H v R) (ball H w R)} ≤ vertexOverlap d R := by
  calc _ ≤ #(ball H v (R + R)) :=
        card_le_card fun w hw => mem_ball_of_not_disjoint H (mem_filter.mp hw).2
    _ ≤ d ^ (R + R + 1) := card_ball_le_degree H hd degree v (R + R)
    _ ≤ vertexOverlap d R := Nat.pow_le_pow_right (by lia) (by lia)

end Locality

/-! ### Threshold events -/

section Events

theorem measurableSet_between {Ω : Type} [MeasurableSpace Ω] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    MeasurableSet {ω | Between t (f ω) (g ω)} := by
  unfold Between
  exact ((measurableSet_lt hf measurable_const).inter (measurableSet_le measurable_const hg)).union
    ((measurableSet_lt hg measurable_const).inter (measurableSet_le measurable_const hf))

end Events

/-! ### Deviations of counts -/

section Deviations

variable {W : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The event that a count of events deviates from its mean by at least `c`. -/
def deviation {κ : Type} (F : Finset κ) (A : κ → Set (W → ℝ)) (c : ℝ) : Set (W → ℝ) :=
  {ω | c ≤ |∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω - ∑ k ∈ F, (gaussPi W).real (A k)|}

omit [DecidableEq W] in
theorem lt_of_notMem_deviation {κ : Type} {F : Finset κ} {A : κ → Set (W → ℝ)} {c : ℝ}
    {ω : W → ℝ} (h : ω ∉ deviation F A c) :
    ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω < ∑ k ∈ F, (gaussPi W).real (A k) + c := by
  simp only [deviation, Set.mem_ofPred_eq, not_le] at h
  linarith [le_abs_self (∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω -
    ∑ k ∈ F, (gaussPi W).real (A k))]

/-- A count of the elements with a property implying an event is at most the number of
events that occur. -/
theorem card_filter_le_sum_indicator {Ω κ : Type} (F : Finset κ) (A : κ → Set Ω) (ω : Ω)
    (p : κ → Prop) [DecidablePred p] (hp : ∀ k ∈ F, p k → ω ∈ A k) :
    (#(F.filter p) : ℝ) ≤ ∑ k ∈ F, (A k).indicator (fun _ => (1 : ℝ)) ω := by
  rw [card_filter]
  push_cast
  refine sum_le_sum fun k hk => ?_
  split_ifs with h
  · rw [Set.indicator_of_mem (hp k hk h)]
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

omit [DecidableEq W] in
/-- At a sample avoiding the deviation event, a count of the elements with a property implying
an event is below the sum of the means plus `c`. -/
theorem card_filter_lt_of_notMem_deviation {κ : Type} {F : Finset κ} {A : κ → Set (W → ℝ)}
    {c : ℝ} {ω : W → ℝ} (h : ω ∉ deviation F A c) (p : κ → Prop) [DecidablePred p]
    (hp : ∀ k ∈ F, p k → ω ∈ A k) :
    (#(F.filter p) : ℝ) < ∑ k ∈ F, (gaussPi W).real (A k) + c :=
  (card_filter_le_sum_indicator F A ω p hp).trans_lt (lt_of_notMem_deviation h)

/-- A set of probability less than one misses some sample. -/
theorem exists_notMem_of_measureReal_lt_one {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {bad : Set Ω} (h : P.real bad < 1) : ∃ ω, ω ∉ bad := by
  by_contra! hall
  rw [Set.eq_univ_of_forall hall, probReal_univ] at h
  exact lt_irrefl _ h

end Deviations

/-! ### Parameters -/

theorem continuous_correlation : Continuous fun q : ℝ => 2 * q / (1 + q ^ 2) :=
  (continuous_const.mul continuous_id).div (continuous_const.add (continuous_pow 2))
    fun q => by positivity

/-- The limiting adjacent correlation of the kernel rows in maximum degree `d`,
`2 √(d - 1) / d`: the neighbour correlation of Gaussian waves on the `d`-regular tree. -/
noncomputable def vertexCorrelation (d : ℕ) : ℝ := 2 * Real.sqrt (d - 1) / d

theorem vertexCorrelation_pos {d : ℕ} (hd : 2 ≤ d) : 0 < vertexCorrelation d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 < (d : ℝ) - 1 := by linarith
  unfold vertexCorrelation
  positivity

/-- The radial kernel reaches every correlation strictly below its limiting value. -/
theorem exists_decay_radius_degree {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : ρ < vertexCorrelation d) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by dsimp [D]; exact_mod_cast hd
  set g := vertexCorrelation d
  set q₀ := Real.sqrt (D - 1) / (D - 1)
  have hu : 0 < D - 1 := by linarith
  have hq₀ : 0 < q₀ := by dsimp [q₀]; positivity
  have hs : Real.sqrt (D - 1) ^ 2 = D - 1 := Real.sq_sqrt hu.le
  have hsq : q₀ ^ 2 = 1 / (D - 1) := by dsimp [q₀]; rw [div_pow, hs]; field_simp
  have hlim : 2 * q₀ / (1 + q₀ ^ 2) = g := by
    rw [hsq]
    dsimp [q₀, g, vertexCorrelation]
    change 2 * (Real.sqrt (D - 1) / (D - 1)) / (1 + 1 / (D - 1)) =
      2 * Real.sqrt (D - 1) / D
    field_simp; ring
  obtain ⟨δ, hδ, hκ⟩ := Metric.continuousAt_iff.mp continuous_correlation.continuousAt
    ((g - ρ) / 2) (by linarith)
  set q := q₀ - min δ q₀ / 2
  have hmin : 0 < min δ q₀ := lt_min hδ hq₀
  have hq0 : 0 ≤ q := by dsimp [q]; linarith [min_le_right δ q₀]
  have hqq : q < q₀ := by dsimp [q]; linarith
  have hκq : g - (g - ρ) / 2 < 2 * q / (1 + q ^ 2) := by
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, show q - q₀ = -(min δ q₀ / 2) by dsimp [q]; ring,
        abs_neg, abs_of_pos (by positivity)]
      linarith [min_le_left δ q₀]
    have H := hκ hdist
    rw [Real.dist_eq, hlim] at H
    linarith [neg_abs_le (2 * q / (1 + q ^ 2) - g)]
  have hdecay : (d - 1 : ℕ) * q ^ 2 < (1 : ℝ) := by
    have hq2 : q ^ 2 < q₀ ^ 2 := by gcongr
    have hq2' := mul_lt_mul_of_pos_left hq2 hu
    rw [hsq, mul_one_div_cancel hu.ne'] at hq2'
    simpa only [Nat.cast_sub (by lia : 1 ≤ d), Nat.cast_one, D] using hq2'
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < (g - ρ) / (2 * D)) hdecay
  have hR' := mul_lt_mul_of_pos_left hR (by linarith : 0 < D)
  have hcancel : D * ((g - ρ) / (2 * D)) = (g - ρ) / 2 := by field_simp
  rw [hcancel] at hR'
  exact ⟨q, R, hq0, by linarith⟩

end Proofs.Gaussian
