/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.Gaussian.Straddle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Gaussian coefficient and its numerical bound

The cubic layout coefficient `p = (3/(2π)) arccos ((1 + 2√2)/4)` of Gaussian edge scores is
positive, and the circuit coefficient `1 + 1/(2p)` is at least `114/25 = 4.56`, by rational
bounds on `√2`, `cos`, and `π`.
-/

@[expose] public section

namespace Proofs.Gaussian

/-- The cubic layout coefficient of Gaussian edge scores, `(3/(2π)) arccos ((1 + 2√2)/4)`. -/
noncomputable def gaussianCoefficient : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)

/-- `p` is the straddling bound at the limiting correlation `2√2/3`. -/
theorem gaussianCoefficient_eq :
    gaussianCoefficient = straddleBound (2 * Real.sqrt 2 / 3) := by
  rw [gaussianCoefficient, straddleBound]
  congr 2
  ring

/-- A crude lower bound, `p ≥ 1/20`, from `cos (π/30) ≥ (1 + 2√2)/4`. -/
theorem gaussianCoefficient_ge : 1 / 20 ≤ gaussianCoefficient := by
  have hsqrt : Real.sqrt 2 < 71 / 50 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpi4 := Real.pi_le_four
  have hθ : Real.pi / 30 ≤ Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := by
    have hcos : (1 + 2 * Real.sqrt 2) / 4 ≤ Real.cos (Real.pi / 30) := by
      have := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 30)
      have hsq : (Real.pi / 30) ^ 2 ≤ (4 / 30) ^ 2 := by gcongr
      linarith
    calc Real.pi / 30 = Real.arccos (Real.cos (Real.pi / 30)) :=
          (Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])).symm
      _ ≤ _ := Real.arccos_le_arccos hcos
  unfold gaussianCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

theorem gaussianCoefficient_pos : 0 < gaussianCoefficient :=
  lt_of_lt_of_le (by norm_num) gaussianCoefficient_ge

/-- The circuit coefficient `1 + 1/(2p)` of the cubic coefficient `p`. -/
theorem one_add_inv_two_mul_gaussianCoefficient :
    1 + 1 / (2 * gaussianCoefficient) =
      1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
  have hsqrt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h : 0 < Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := Real.arccos_pos.mpr (by linarith)
  unfold gaussianCoefficient
  congr 1
  field_simp

/-- The exact Gaussian circuit coefficient is at least `114/25 = 4.56`.

With `θ = arccos ((1 + 2√2)/4) = 0.293950…`, the bound `θ ≤ 0.2941` has a margin of
`1.5 · 10⁻⁴`, and `π / (3 · 0.2941) = 3.5607…` exceeds `89/25 = 3.56` by `6 · 10⁻⁴`. The cosine
is bounded at the half angle `0.14705` by its Taylor polynomial and doubled:
`2 cos² (0.14705) - 1 ≤ 0.957083…`, against `(1 + 2√2)/4 = 0.957107…`. -/
theorem circuitCoefficient_ge_456 :
    (114 / 25 : ℝ) ≤ 1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
  have hsqrt : (141421 : ℝ) / 100000 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hsqrt' : Real.sqrt 2 < 3 / 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have ha : 0 < Real.arccos ((1 + 2 * Real.sqrt 2) / 4) :=
    Real.arccos_pos.mpr (by linarith)
  have hcos : Real.cos (2941 / 10000) ≤ (1 + 2 * Real.sqrt 2) / 4 := by
    have hb := Real.cos_bound (x := 2941 / 20000) (by norm_num)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2941 / 20000)] at hb
    have hlo := Real.one_sub_sq_div_two_le_cos (x := 2941 / 20000)
    have hnonneg : 0 ≤ Real.cos (2941 / 20000) := by linarith
    have hupper : Real.cos (2941 / 20000) ≤
        1 - (2941 / 20000 : ℝ) ^ 2 / 2 + (2941 / 20000 : ℝ) ^ 4 * (5 / 96) := by
      linarith [(abs_le.mp hb).2]
    have hsq := pow_le_pow_left₀ hnonneg hupper 2
    rw [show (2941 / 10000 : ℝ) = 2 * (2941 / 20000) by ring, Real.cos_two_mul]
    nlinarith [hsq, hsqrt]
  have hangle : Real.arccos ((1 + 2 * Real.sqrt 2) / 4) ≤ 2941 / 10000 :=
    (Real.arccos_le_arccos hcos).trans_eq
      (Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_d6]))
  have hdiv : (89 / 25 : ℝ) ≤ Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_gt_d6, hangle]
  linarith

end Proofs.Gaussian
