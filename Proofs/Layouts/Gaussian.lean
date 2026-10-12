/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Gaussian.Sample
public import Proofs.Layouts.Gaussian.Coefficient

/-!
# Gaussian layouts of cubic graphs

Every large simple cubic graph on `h` vertices has a layout whose prefixes are crossed by at
most `(p + ξ) h + 2` edges, where

`p = (3/(2π)) arccos ((1 + 2√2)/4) ≈ 0.14035`

is `gaussianCoefficient` (`cubicLayoutBound_gaussian`).

**The random layout.** Give each vertex `v` its unit kernel row `x_v` (`Proofs.Layouts.Kernel`):
the normalized vector of distance weights `q ^ dist(v, z)`, truncated at radius `R`. Give each
edge `uv` the unit vector `y_uv` in the direction of `x_u + x_v`. Draw a standard Gaussian vector
`ω` and score each edge by `⟨y_e, ω⟩`. List the vertices by the median of their three edge
scores (`Proofs.Layouts.Median`).

**One vertex.** A vertex straddles a threshold when two of its edge scores fall on opposite
sides. The three edge vectors at `v` have correlation at least `√((1 + ρ)/2)` with `x_v`, where
`ρ` bounds the correlation of adjacent rows; by Sheppard's bound a pair with correlation `ρ'`
is separated with probability at most `arccos ρ' / π`, and the star inequality
(`Proofs.Layouts.Star`) bounds the probability that `v` straddles any fixed threshold by
`(3/(2π)) arccos ((1 + 3ρ)/4)` (`measureReal_straddleEvent_le`).

**All thresholds at once.** Each event depends only on the coordinates of `ω` in a ball of
bounded radius, so each count of events has variance `O(h)` and is within `ε h` of its mean
with probability `1 - O(1/h)` (`Proofs.Layouts.SecondMoment`). For large `h` one sample keeps
the straddling counts at a grid of thresholds, the window counts between them, and the tails
near their means (`exists_good_sample`); the median layout of that sample has every prefix cut
at most `(p_ρ + O(δ) + O(ε) + O(1/T^2)) h`.

**The limit.** As `q` increases to `1/√2` and `R` grows, the adjacent correlation tends to
`2√2/3`, the neighbour correlation of Gaussian waves on the 3-regular tree, and
`(1 + 3 · 2√2/3)/4 = (1 + 2√2)/4`.
-/

@[expose] public section

namespace Proofs.Gaussian

open MeasureTheory ProbabilityTheory Finset

/-! ### Parameters -/

/-- **Decay rate and radius.** Every `ρ₀ < 2√2/3` admits a nonnegative decay rate `q` and a
radius `R` such that `ρ₀ ≤ 2q/(1+q²) - 3(2q²)^R`. -/
theorem exists_decay_radius {ρ₀ : ℝ} (hρ₀g : ρ₀ < 2 * Real.sqrt 2 / 3) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧ ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by
  have h3 : vertexCorrelation 3 = 2 * Real.sqrt 2 / 3 := by norm_num [vertexCorrelation]
  obtain ⟨q, R, hq, hρ⟩ :=
    exists_decay_radius_degree (by norm_num : 2 ≤ 3) (ρ := ρ₀) (by rw [h3]; exact hρ₀g)
  exact ⟨q, R, hq, by simpa using hρ⟩

/-- **Parameters.** For every positive slack some admissible parameters bring the per-vertex
cut bound within that slack of `gaussianCoefficient`. -/
theorem exists_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ 1 / 8 ≤ ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      cubicBound ρ₀ T ε M ≤ gaussianCoefficient + ξ := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  -- A correlation target `ρ₀ < g` with a nearly optimal straddling bound.
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    ((Real.continuous_arccos.comp (by fun_prop : Continuous fun ρ : ℝ => (1 + 3 * ρ) / 4)
      ).continuousAt (x := g)) (Real.pi * ξ / 6) (by positivity)
  set ρ₀ := g - min η (1 / 4) / 2 with hρ₀
  have hmin : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by rw [hρ₀]; linarith
  have hρ₀low : 1 / 8 ≤ ρ₀ := by rw [hρ₀, hg]; linarith [min_le_right η (1 / 4)]
  have hbound : straddleBound ρ₀ ≤ gaussianCoefficient + ξ / 4 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
      linarith [min_le_left η (1 / 4)]
    have := hcont hdist
    simp only [Function.comp_apply, Real.dist_eq] at this
    have hle := (le_abs_self _).trans this.le
    rw [straddleBound, gaussianCoefficient_eq, ← hg, straddleBound]
    have hpi : 0 < Real.pi := Real.pi_pos
    calc 3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4)
        ≤ 3 / (2 * Real.pi) * (Real.arccos ((1 + 3 * g) / 4) + Real.pi * ξ / 6) := by
          gcongr; linarith
      _ = 3 / (2 * Real.pi) * Real.arccos ((1 + 3 * g) / 4) + ξ / 4 := by field_simp; ring
  obtain ⟨q, R, hq0, hρ⟩ := exists_decay_radius hρ₀g
  -- The grid and the deviation slack.
  set ε := min (ξ / 12) (1 / 100) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈720 / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 720 / ξ ≤ M := by rw [hM]; push_cast; linarith [Nat.le_ceil (720 / ξ)]
  refine ⟨q, R, ρ₀, 20, ε, M, hq0, hρ₀low, hρ, by norm_num, hεpos, hMpos, ?_⟩
  have hcoef := gaussianCoefficient_ge
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine max_le ?_ ?_
  · have : ε ≤ 1 / 100 := min_le_right _ _
    linarith
  · have hεξ : ε ≤ ξ / 12 := min_le_left _ _
    have hsqrtpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.two_le_pi])
    have hgrid : 9 / 2 * (2 * 20 / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      calc 9 / 2 * (2 * 20 / (M : ℝ)) = 180 / M := by ring
        _ ≤ ξ / 2 := by
            rw [div_le_iff₀ hMpos']
            have := mul_le_mul_of_nonneg_left hMR hξ.le
            rw [mul_div_cancel₀ _ hξ.ne'] at this
            linarith
        _ ≤ ξ / 4 * Real.sqrt (2 * Real.pi) := by nlinarith
    linarith

/-- **Gaussian layouts of cubic graphs.** For every `ξ > 0`, every sufficiently large simple
cubic graph on `h` vertices has a layout whose prefixes are crossed by at most
`(gaussianCoefficient + ξ) h + 2` edges. -/
theorem cubicLayoutBound_gaussian : CubicLayoutBound gaussianCoefficient := by
  intro ξ hξ
  obtain ⟨q, R, ρ₀, T, ε, M, hq0, hρ₀, hρ, hT, hε, hM, hbound⟩ := exists_parameters hξ
  refine ⟨⌈(3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2⌉₊,
    fun W _ _ H _ regular large => ?_⟩
  have large' : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨key, hinj, hcut⟩ := exists_good_sample regular hq0 R hρ₀ hρ hT hε hM large'
  refine ⟨key, hinj, fun t => (hcut t).trans ?_⟩
  have hh0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hbound hh0]

end Proofs.Gaussian
