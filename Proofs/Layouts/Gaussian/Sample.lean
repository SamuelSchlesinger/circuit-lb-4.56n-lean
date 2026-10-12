/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Gaussian.Straddle
public import Proofs.Layouts.SecondMoment

/-!
# One sample controls every median-layout cut

Apply the second-moment bound to straddles, score windows, and tails. A finite union bound
gives one sample satisfying all estimates needed by the deterministic median-layout lemma.
-/

@[expose] public section

namespace Proofs.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-! ### A good sample -/

section Sample

variable {W : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]

omit [DecidableEq W] in
/-- A cubic graph on `h` vertices has `3h/2` edges. -/
theorem card_edgeFinset_of_regular (regular : H.IsRegularOfDegree 3) :
    (#H.edgeFinset : ℝ) = 3 / 2 * Fintype.card W := by
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [regular.degree_eq, sum_const, card_univ, smul_eq_mul] at hsum
  have : ((Fintype.card W * 3 : ℕ) : ℝ) = ((2 * #H.edgeFinset : ℕ) : ℝ) := by
    exact_mod_cast hsum
  push_cast at this
  linarith

variable (H) in
/-- An event about one edge score. -/
def edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) : Set (W → ℝ) :=
  {ω | p (edgeScore H q R ω e)}

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_edgeScoreEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (e : Sym2 W) :
    MeasurableSet (edgeScoreEvent H q R p e) :=
  measurable_edgeScore H q R e hp

omit [DecidableRel H.Adj] in
theorem dependsOn_edgeScoreEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (e : Sym2 W) :
    DependsOn (· ∈ edgeScoreEvent H q R p e) (edgeSupport H R e : Set W) := by
  intro ω ω' h
  simp only [edgeScoreEvent, Set.mem_ofPred_eq]
  rw [edgeScore_congr le_rfl fun i hi => h i hi]

omit [DecidableEq W] in
/-- The edge vectors of a graph with large kernel correlations are unit vectors. -/
theorem sum_edgeVector_sq_of_mem (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q)
    {R : ℕ} {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {e : Sym2 W} (he : e ∈ H.edgeFinset) : ∑ z, edgeVector H q R e z ^ 2 = 1 := by
  induction e using Sym2.ind with
  | _ u v =>
  have hcorr := hρ.trans (sum_unitKernel_mul_ge H degree hq0 R (SimpleGraph.mem_edgeFinset.mp he))
  exact sum_edgeVector_sq (by rw [pairNormSq_eq]; linarith)

/-- The prefix-cut bound of the median layout, per vertex, with the given parameters. -/
noncomputable def cubicBound (ρ₀ T ε : ℝ) (M : ℕ) : ℝ :=
  max (9 / (2 * T ^ 2) + 3 * ε)
    (straddleBound ρ₀ + 9 / 2 * (2 * T / M) / Real.sqrt (2 * Real.pi) + 4 * ε)

/-- The prefix-cut bound of the median layout, per vertex, when the expected number of vertices
straddling any threshold is at most `μ` per vertex. -/
noncomputable def cubicBoundOfMean (μ T ε : ℝ) (M : ℕ) : ℝ :=
  max (9 / (2 * T ^ 2) + 3 * ε)
    (μ + 9 / 2 * (2 * T / M) / Real.sqrt (2 * Real.pi) + 4 * ε)

/-- The four concentration estimates needed by the deterministic median-layout step. -/
private structure SampleConcentration (q : ℝ) (R : ℕ) (T ε : ℝ) (M : ℕ)
    (ω : W → ℝ) : Prop where
  straddle (i : ℕ) (hi : i < M) :
    ω ∉ deviation univ (straddleEvent H q R (-T + i * (2 * T / M))) (ε * Fintype.card W)
  window (i : ℕ) (hi : i < M) :
    ω ∉ deviation H.edgeFinset
      (edgeScoreEvent H q R (fun x => -T + i * (2 * T / M) ≤ x ∧
        x < -T + i * (2 * T / M) + 2 * T / M)) (ε * Fintype.card W)
  low : ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R (· < -T)) (ε * Fintype.card W)
  high : ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R (T ≤ ·)) (ε * Fintype.card W)

omit [DecidableEq W] in
/-- For a large cubic graph some sample satisfies all four concentration estimates: by the
second-moment bound, the deviation events have total probability less than one. -/
private theorem exists_concentrated_sample (regular : H.IsRegularOfDegree 3)
    (q : ℝ) (R : ℕ) (T : ℝ) {ε : ℝ} (hε : 0 < ε) (M : ℕ)
    (large : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ ω, SampleConcentration (H := H) q R T ε M ω := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card W : ℝ)
  set P := gaussPi W
  set Dn : ℝ := (vertexOverlap 3 (R + 1) : ℝ)
  set δ : ℝ := 2 * T / M
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hcpos : 0 < c := mul_pos hε hhpos
  have hE := card_edgeFinset_of_regular regular
  -- The thresholds and the four families of events.
  let thr : ℕ → ℝ := fun i => -T + i * δ
  let straddle : ℕ → W → Set (W → ℝ) := fun i => straddleEvent H q R (thr i)
  let window : ℕ → Sym2 W → Set (W → ℝ) := fun i =>
    edgeScoreEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => x < -T)
  let high : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => T ≤ x)
  let bad : Set (W → ℝ) :=
    ((⋃ i ∈ range M,
      (deviation univ (straddle i) c ∪ deviation H.edgeFinset (window i) c)) ∪
      deviation H.edgeFinset low c) ∪ deviation H.edgeFinset high c
  -- Each count deviates from its mean by `c` with probability `O(1/h)`.
  have straddleDev : ∀ i, P.real (deviation univ (straddle i) c) ≤ h * Dn / c ^ 2 := by
    intro i
    have := pi_deviation_le (fun _ : W => gaussianReal 0 1) univ (straddle i)
      (fun v => ball H v (R + 1)) (fun v _ => measurableSet_straddleEvent q R (thr i) v)
      (fun v _ => dependsOn_straddleEvent q R (thr i) v)
      (fun v _ => ball_overlap_le H (by norm_num) degree (R + 1) v) hcpos
    rwa [card_univ] at this
  have edgeDev : ∀ (A : Sym2 W → Set (W → ℝ)), (∀ e, MeasurableSet (A e)) →
      (∀ e, DependsOn (· ∈ A e) (edgeSupport H R e : Set W)) →
      P.real (deviation H.edgeFinset A c) ≤ #H.edgeFinset * Dn / c ^ 2 := by
    intro A hA hdep
    refine (pi_deviation_le (fun _ : W => gaussianReal 0 1) H.edgeFinset A (edgeSupport H R)
      (fun e _ => hA e) (fun e _ => hdep e)
      (fun e he => edge_overlap_le H (by norm_num) degree R he) hcpos).trans ?_
    have : vertexOverlap 3 R ≤ vertexOverlap 3 (R + 1) := by
      unfold vertexOverlap; exact Nat.pow_le_pow_right (by norm_num) (by lia)
    gcongr
    simp only [Dn]
    exact_mod_cast this
  have edgeDev' : ∀ {p : ℝ → Prop}, MeasurableSet {x | p x} →
      P.real (deviation H.edgeFinset (edgeScoreEvent H q R p) c) ≤
        #H.edgeFinset * Dn / c ^ 2 := fun hp =>
    edgeDev _ (fun e => measurableSet_edgeScoreEvent q R hp e)
      (fun e => dependsOn_edgeScoreEvent q R _ e)
  have hbad : P.real bad < 1 := by
    have hunion : P.real bad ≤ ∑ i ∈ range M,
        (h * Dn / c ^ 2 + #H.edgeFinset * Dn / c ^ 2) +
          #H.edgeFinset * Dn / c ^ 2 + #H.edgeFinset * Dn / c ^ 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (edgeDev' (measurableSet_le measurable_const measurable_id)))
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (edgeDev' (measurableSet_lt measurable_id measurable_const)))
      refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun i _ => ?_)
      exact (measureReal_union_le _ _).trans (add_le_add (straddleDev i)
        (edgeDev' ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_lt measurable_id measurable_const))))
    rw [sum_const, card_range, nsmul_eq_mul, hE] at hunion
    refine hunion.trans_lt ?_
    have hD : 0 ≤ Dn := by positivity
    have key : (M * (h * Dn / c ^ 2 + 3 / 2 * h * Dn / c ^ 2) + 3 / 2 * h * Dn / c ^ 2 +
        3 / 2 * h * Dn / c ^ 2) = (5 / 2 * M + 3) * Dn / ε ^ 2 / h := by
      rw [hc]; field_simp; ring
    rw [key, div_lt_one hhpos]
    calc (5 / 2 * (M : ℝ) + 3) * Dn / ε ^ 2 ≤ (3 * M + 3) * Dn / ε ^ 2 := by
          gcongr; linarith
      _ < h := large
  obtain ⟨ω, hω⟩ := exists_notMem_of_measureReal_lt_one hbad
  simp only [bad, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  obtain ⟨⟨hmid, hlow⟩, hhigh⟩ := hω
  exact ⟨ω, fun i hi => (hmid i (mem_range.mpr hi)).1,
    fun i hi => (hmid i (mem_range.mpr hi)).2, hlow, hhigh⟩

omit [DecidableEq W] in
/-- If every threshold is straddled by at most `h μ` vertices in expectation, some Gaussian
sample yields a median layout all of whose prefixes are crossed by at most
`h · cubicBoundOfMean μ T ε M` edges. -/
theorem exists_good_sample_of_mean (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    (R : ℕ) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W)
    {μ : ℝ} (hmean : ∀ t, (∑ v, (gaussPi W).real (straddleEvent H q R t v)) ≤
      Fintype.card W * μ) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      (#(H.cutFinset {w | key w < t}) : ℝ) ≤ Fintype.card W * cubicBoundOfMean μ T ε M := by
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card W : ℝ)
  set P := gaussPi W
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := 2 * T / M with hδ
  have hδpos : 0 < δ := by positivity
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hE := card_edgeFinset_of_regular regular
  have unit := fun {e : Sym2 W} (he : e ∈ H.edgeFinset) =>
    sum_edgeVector_sq_of_mem degree hq0 hρ₀ hρ he
  obtain ⟨ω, good⟩ := exists_concentrated_sample regular q R T hε M large
  let thr : ℕ → ℝ := fun i => -T + i * δ
  let straddle : ℕ → W → Set (W → ℝ) := fun i => straddleEvent H q R (thr i)
  let low : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => x < -T)
  let high : Sym2 W → Set (W → ℝ) := edgeScoreEvent H q R (fun x => T ≤ x)
  set X := edgeScore H q R ω
  -- The means of the counts.
  have edgeMean : ∀ {p : ℝ → Prop} {b : ℝ}, (∀ e ∈ H.edgeFinset,
      P.real (edgeScoreEvent H q R p e) ≤ b) →
      ∑ e ∈ H.edgeFinset, P.real (edgeScoreEvent H q R p e) ≤ #H.edgeFinset * b :=
    fun hb => (sum_le_sum hb).trans_eq (by rw [sum_const, nsmul_eq_mul])
  have tailMean : ∀ e ∈ H.edgeFinset, P.real (low e) ≤ 1 / T ^ 2 ∧ P.real (high e) ≤ 1 / T ^ 2 :=
    fun e he => ⟨(measureReal_mono fun ω' hω' => by
      simp only [low, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
      rw [abs_of_neg (by linarith)]; linarith).trans (gaussPi_tail_le _ (unit he) hT),
      (measureReal_mono fun ω' hω' => by
      simp only [high, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
      exact hω'.trans (le_abs_self _)).trans (gaussPi_tail_le _ (unit he) hT)⟩
  -- A count below its mean plus `c`, for edges in a tail.
  have tail : ∀ (p : ℝ → Prop) [DecidablePred p],
      (∀ e ∈ H.edgeFinset, P.real (edgeScoreEvent H q R p e) ≤ 1 / T ^ 2) →
      ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R p) c →
      3 * (#{e ∈ H.edgeFinset | p (X e)} : ℝ) ≤ h * (9 / (2 * T ^ 2) + 3 * ε) := by
    intro p _ hmean hdev
    have hcount := card_filter_lt_of_notMem_deviation hdev (fun e => p (X e)) fun e _ hpe => hpe
    have := edgeMean hmean
    calc 3 * (#{e ∈ H.edgeFinset | p (X e)} : ℝ)
        ≤ 3 * (#H.edgeFinset * (1 / T ^ 2) + c) := by linarith
      _ = h * (9 / (2 * T ^ 2) + 3 * ε) := by rw [hE, hc]; field_simp; ring
  have hB1 : h * (9 / (2 * T ^ 2) + 3 * ε) ≤ h * cubicBoundOfMean μ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (μ + 9 / 2 * δ / Real.sqrt (2 * Real.pi) + 4 * ε) ≤
      h * cubicBoundOfMean μ T ε M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  obtain ⟨key, hinj, hcut⟩ := exists_key_of_edgeScore regular X hδpos M
    (a := -T) (B := h * cubicBoundOfMean μ T ε M)
    ((tail (· < -T) (fun e he => (tailMean e he).1) good.low).trans hB1)
    (by
      have hT' : -T + M * δ = T := by rw [hδ]; field_simp; ring
      rw [hT']
      exact (tail (T ≤ ·) (fun e he => (tailMean e he).2) good.high).trans hB1)
    (by
      intro i hi
      have hScount := card_filter_lt_of_notMem_deviation (good.straddle i hi)
        (fun v => EdgeStraddles H X (-T + i * δ) v) fun v _ hv => hv
      have hWcount := card_filter_lt_of_notMem_deviation (good.window i hi)
        (fun e => -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ) fun e _ he =>
          ⟨he.1, by linarith [he.2, hδ]⟩
      have hSmean : ∑ v, P.real (straddle i v) ≤ h * μ := hmean (thr i)
      have hWmean := edgeMean (p := fun x => thr i ≤ x ∧ x < thr i + δ)
        (b := δ / Real.sqrt (2 * Real.pi)) fun e he =>
        gaussPi_window_le _ (unit he) (thr i) hδpos.le
      calc (#{v | EdgeStraddles H X (-T + i * δ) v} : ℝ) +
            3 * #{e ∈ H.edgeFinset | -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ}
          ≤ (h * μ + c) +
              3 * (#H.edgeFinset * (δ / Real.sqrt (2 * Real.pi)) + c) := by
            gcongr
            · linarith
            · linarith
        _ = h * (μ + 9 / 2 * δ / Real.sqrt (2 * Real.pi) + 4 * ε) := by
            rw [hE, hc]; ring
        _ ≤ _ := hB2)
  exact ⟨key, hinj, fun t => (hcut t).trans_eq (by ring)⟩

omit [DecidableEq W] in
/-- **A good sample.** For a large cubic graph some Gaussian sample yields a median layout all
of whose prefixes are crossed by at most `h · cubicBound ρ₀ T ε M` edges. -/
theorem exists_good_sample (regular : H.IsRegularOfDegree 3) {q : ℝ} (hq0 : 0 ≤ q)
    (R : ℕ) {ρ₀ : ℝ} (hρ₀ : 1 / 8 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      (#(H.cutFinset {w | key w < t}) : ℝ) ≤ Fintype.card W * cubicBound ρ₀ T ε M := by
  apply exists_good_sample_of_mean regular hq0 R (by linarith) hρ hT hε hM large
  intro t
  have h := sum_le_sum (s := univ) fun v (_ : v ∈ (univ : Finset W)) =>
    measureReal_straddleEvent_le regular hq0 hρ₀ hρ t v
  simpa only [sum_const, card_univ, nsmul_eq_mul] using h

end Sample

end Proofs.Gaussian
