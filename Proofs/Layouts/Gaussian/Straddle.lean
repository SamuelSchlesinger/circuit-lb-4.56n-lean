/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Gaussian.EdgeScores
public import Proofs.Layouts.Median
public import Proofs.Layouts.Star

/-!
# The straddling probability of one vertex

The three edge vectors at a cubic vertex form a star. Sheppard's bound and the star inequality
bound the probability that their scores fall on both sides of a fixed threshold.
-/

@[expose] public section

namespace Proofs.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-! ### The straddling probability of one vertex -/

section Straddle

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The straddling probability bound `(3/(2π)) arccos ((1 + 3ρ₀)/4)`, for adjacent kernel rows
with correlation at least `ρ₀`. -/
noncomputable def straddleBound (ρ₀ : ℝ) : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4)

/-- The event that the edge scores at `v` straddle the threshold `t`. -/
def straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) : Set (W → ℝ) :=
  {ω | EdgeStraddles H (edgeScore H q R ω) t v}

variable {H}

omit [DecidableEq W] in
/-- The edge vectors at `v` are unit vectors with correlation at least `√((1 + ρ₀)/2)` with the
row of `v`. -/
theorem edgeVector_star (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q) {R : ℕ}
    {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (v : W) {e : Sym2 W} (he : e ∈ H.incidenceFinset v) :
    ∑ z, edgeVector H q R e z ^ 2 = 1 ∧
      Real.sqrt ((1 + ρ₀) / 2) ≤ ∑ z, edgeVector H q R e z * unitKernel H q R v z := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_sep_iff] at he
  obtain ⟨hedge, hv⟩ := he
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
  have hadj : H.Adj u v := (SimpleGraph.mem_edgeSet H).mp hedge |>.symm
  have hcorr := hρ.trans (sum_unitKernel_mul_ge H degree hq0 R hadj)
  have hpos : 0 < pairNormSq H q R u v := by rw [pairNormSq_eq]; linarith
  rw [Sym2.eq_swap]
  refine ⟨sum_edgeVector_sq hpos, ?_⟩
  rw [sum_edgeVector_mul hpos]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Three reals on both sides of a threshold give four separated ordered pairs. -/
theorem four_le_between_pairs {t p q r : ℝ} (hlt : p < t ∨ q < t ∨ r < t)
    (hge : t ≤ p ∨ t ≤ q ∨ t ≤ r) :
    (4 : ℝ) ≤ ((if Between t p q then 1 else 0) + (if Between t p r then 1 else 0)) +
      (((if Between t q p then 1 else 0) + (if Between t q r then 1 else 0)) +
        ((if Between t r p then 1 else 0) + (if Between t r q then 1 else 0))) := by
  grind [Between]

/-- A straddling vertex of a cubic graph has at least four separated ordered pairs of edges. -/
theorem indicator_edgeStraddles_le (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) (t : ℝ) (v : W) :
    (if EdgeStraddles H score t v then (1 : ℝ) else 0) ≤
      1 / 4 * ∑ e ∈ H.incidenceFinset v, ∑ e' ∈ (H.incidenceFinset v).erase e,
        if Between t (score e) (score e') then (1 : ℝ) else 0 := by
  split_ifs with h
  swap
  · refine mul_nonneg (by norm_num) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => ?_)
    split_ifs <;> norm_num
  obtain ⟨e₁, he₁, h₁, e₂, he₂, h₂⟩ := h
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ :=
    card_eq_three.mp (card_incidenceFinset_of_regular regular v)
  rw [hs] at he₁ he₂ ⊢
  have hlt : score x < t ∨ score y < t ∨ score z < t := by
    simp only [mem_insert, mem_singleton] at he₁
    rcases he₁ with rfl | rfl | rfl <;> simp [h₁]
  have hge : t ≤ score x ∨ t ≤ score y ∨ t ≤ score z := by
    simp only [mem_insert, mem_singleton] at he₂
    rcases he₂ with rfl | rfl | rfl <;> simp [h₂]
  have ex : ({x, y, z} : Finset (Sym2 W)).erase x = {y, z} := by
    ext; simp only [mem_erase, mem_insert, mem_singleton]; grind
  have ey : ({x, y, z} : Finset (Sym2 W)).erase y = {x, z} := by
    ext; simp only [mem_erase, mem_insert, mem_singleton]; grind
  have ez : ({x, y, z} : Finset (Sym2 W)).erase z = {x, y} := by
    ext; simp only [mem_erase, mem_insert, mem_singleton]; grind
  rw [sum_insert (by simp [hxy, hxz]), sum_insert (by simp [hyz]), sum_singleton, ex, ey, ez,
    sum_pair hyz, sum_pair hxz, sum_pair hxy]
  have := four_le_between_pairs hlt hge
  linarith

omit [DecidableEq W] in
theorem measurableSet_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) :
    MeasurableSet (straddleEvent H q R t v) := by
  have : straddleEvent H q R t v = ⋃ e ∈ H.incidenceFinset v,
      ({ω | edgeScore H q R ω e < t} ∩
        ⋃ e' ∈ H.incidenceFinset v, {ω | t ≤ edgeScore H q R ω e'}) := by
    ext ω
    simp only [straddleEvent, EdgeStraddles, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff, exists_prop]
  rw [this]
  refine measurableSet_biUnion _ fun e _ => ?_
  exact (measurableSet_lt (measurable_edgeScore H q R e) measurable_const).inter
    (measurableSet_biUnion _ fun e' _ =>
      measurableSet_le measurable_const (measurable_edgeScore H q R e'))

omit [DecidableEq W] in
/-- Whether `v` straddles a threshold depends only on the ball of radius `R + 1` around `v`. -/
theorem dependsOn_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : W) :
    DependsOn (· ∈ straddleEvent H q R t v) (ball H v (R + 1) : Set W) := by
  classical
  intro ω ω' h
  have hscore : ∀ e ∈ H.incidenceFinset v, edgeScore H q R ω e = edgeScore H q R ω' e :=
    fun e he => edgeScore_congr (edgeSupport_subset_ball he) fun i hi => h i hi
  simp only [straddleEvent, Set.mem_ofPred_eq, EdgeStraddles]
  apply propext
  constructor
  · rintro ⟨e, he, h1, e', he', h2⟩
    exact ⟨e, he, hscore e he ▸ h1, e', he', hscore e' he' ▸ h2⟩
  · rintro ⟨e, he, h1, e', he', h2⟩
    exact ⟨e, he, (hscore e he).symm ▸ h1, e', he', (hscore e' he').symm ▸ h2⟩

/-- In a 3-regular graph, assume `q ≥ 0`, `ρ₀ ≥ 1/8`, and that the explicit truncated-kernel
correlation bound is at least `ρ₀`. If the inner products of the edge vectors at `v` over
ordered pairs sum to at least `6 a`, then `v` straddles any fixed threshold with probability
at most `(3/(2π)) arccos a`. -/
theorem measureReal_straddleEvent_le_of_average (regular : H.IsRegularOfDegree 3)
    {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 1 / 8 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : W)
    {a : ℝ} (haverage : 6 * a ≤ ∑ e ∈ H.incidenceFinset v,
      ∑ e' ∈ (H.incidenceFinset v).erase e,
        ∑ z, edgeVector H q R e z * edgeVector H q R e' z) :
    (gaussPi W).real (straddleEvent H q R t v) ≤ 3 / (2 * Real.pi) * Real.arccos a := by
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set κ := Real.sqrt ((1 + ρ₀) / 2) with hκ
  have hκ34 : 3 / 4 ≤ κ := by
    rw [hκ, show (3 / 4 : ℝ) = Real.sqrt ((3 / 4) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have star := fun e (he : e ∈ H.incidenceFinset v) =>
    edgeVector_star degree hq0 (by linarith) hρ v he
  set s := H.incidenceFinset v
  have hs : #s = 3 := card_incidenceFinset_of_regular regular v
  have hxv := sum_unitKernel_sq H q R v
  -- Pairwise correlations are large.
  have pair : ∀ e ∈ s, ∀ e' ∈ s, -1 < ∑ z, edgeVector H q R e z * edgeVector H q R e' z := by
    intro e he e' he'
    have := le_inner_of_le_inner hxv (star e he).1 (star e' he').1 (star e he).2 (star e' he').2
    linarith
  -- The pointwise counting inequality, integrated.
  have hint : ∀ e e', Integrable ({ω : W → ℝ |
      Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}.indicator 1) (gaussPi W) :=
    fun e e' => (integrable_const (1 : ℝ)).indicator
      (measurableSet_between (measurable_edgeScore H q R e) (measurable_edgeScore H q R e') t)
  have count : (gaussPi W).real (straddleEvent H q R t v) ≤
      1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
        (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')} := by
    rw [← integral_indicator_one (measurableSet_straddleEvent q R t v)]
    have hpt : ∀ ω, (straddleEvent H q R t v).indicator (1 : (W → ℝ) → ℝ) ω ≤
        1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          {ω : W → ℝ | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}.indicator 1 ω := by
      intro ω
      have := indicator_edgeStraddles_le regular (edgeScore H q R ω) t v
      simp only [Set.indicator_apply, straddleEvent, Set.mem_ofPred_eq, Pi.one_apply]
      convert this using 1
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg
      (fun _ _ => zero_le_one) ω) ?_ (Filter.Eventually.of_forall hpt)).trans_eq ?_
    · exact Integrable.const_mul (integrable_finsetSum _ fun e _ =>
        integrable_finsetSum _ fun e' _ => hint e e') _
    · rw [integral_const_mul, integral_finsetSum _ fun e _ =>
        integrable_finsetSum _ fun e' _ => hint e e']
      congr 1
      refine sum_congr rfl fun e _ => ?_
      rw [integral_finsetSum _ fun e' _ => hint e e']
      exact sum_congr rfl fun e' _ => integral_indicator_one (measurableSet_between
        (measurable_edgeScore H q R e) (measurable_edgeScore H q R e') t)
  refine count.trans ?_
  -- Sheppard's bound for each separated pair, then the star inequality.
  have hsum := sum_arccos_star_le_of_average hxv s hs (fun e => edgeVector H q R e)
    (fun e he => (star e he).1) hκ34 (fun e he => (star e he).2) haverage
  calc 1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
        (gaussPi W).real {ω | Between t (edgeScore H q R ω e) (edgeScore H q R ω e')}
      ≤ 1 / 4 * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) / Real.pi := by
        gcongr with e he e' he'
        exact gaussPi_between_le_arccos (star e he).1 (star e' (mem_of_mem_erase he')).1
          (pair e he e' (mem_of_mem_erase he')) t
    _ = 1 / 4 / Real.pi * ∑ e ∈ s, ∑ e' ∈ s.erase e,
          Real.arccos (∑ z, edgeVector H q R e z * edgeVector H q R e' z) := by
        simp only [div_eq_mul_inv, ← sum_mul]; ring
    _ ≤ 1 / 4 / Real.pi * (6 * Real.arccos a) := by gcongr
    _ = 3 / (2 * Real.pi) * Real.arccos a := by ring

omit [DecidableEq W] in
/-- **Straddling probability.** If adjacent kernel rows have correlation at least `ρ₀ ≥ 1/8`,
a vertex straddles any fixed threshold with probability at most `straddleBound ρ₀`. -/
theorem measureReal_straddleEvent_le (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 1 / 8 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : W) :
    (gaussPi W).real (straddleEvent H q R t v) ≤ straddleBound ρ₀ := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  have star := fun e (he : e ∈ H.incidenceFinset v) =>
    edgeVector_star degree hq0 (by linarith) hρ v he
  apply measureReal_straddleEvent_le_of_average regular hq0 hρ₀ hρ
  have hsum := sum_inner_ordered_pairs_ge (sum_unitKernel_sq H q R v)
    (H.incidenceFinset v) (fun e => edgeVector H q R e)
    (fun e he => (star e he).1) (Real.sqrt_nonneg ((1 + ρ₀) / 2))
    (fun e he => (star e he).2)
  rw [card_incidenceFinset_of_regular regular v, Real.sq_sqrt (by linarith)] at hsum
  push_cast at hsum
  linarith

end Straddle

end Proofs.Gaussian
