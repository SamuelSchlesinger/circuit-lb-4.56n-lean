/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Statement
import Proofs.Circuit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Proofs.Layouts
import Proofs.LowerBound
import Proofs.AverageCase

/-!
# The lower-bound theorems

Under the hypotheses of `CircuitLowerBound` in `Statement.lean`, the vertex-score proof
gives coefficient four. The median edge-score proof gives the exact Gaussian coefficient
and the checked rational coefficient `114/25 = 4.56`. The same three coefficients hold for the
average-case claim `AverageCaseBound`. Each theorem has its own axiom check.
-/

namespace Proofs

/-- **Circuits of fan-in two need `(4 - ε) n` gates**, by Gaussian vertex-score layouts. -/
public theorem lowerBound_four : CircuitLowerBound 4 := by
  intro U _ _ S K hfree hK hdense ε hε
  have h := lowerBound_fanInTwo (by norm_num) layoutBound_one_third S K hfree hK hdense hε
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-- info: 'Proofs.lowerBound_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerBound_four

/-- **Circuits of fan-in two need `(L - ε) n` gates**, by median edge-score layouts, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625` is the exact Gaussian coefficient. -/
public theorem lowerBound_gaussian :
    CircuitLowerBound (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4))) := by
  intro U _ _ S K hfree hK hdense ε hε
  have h := lowerBound_fanInTwo (mul_pos two_pos Gaussian.gaussianCoefficient_pos)
    layoutBound_gaussian S K hfree hK hdense hε
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/--
info: 'Proofs.lowerBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lowerBound_gaussian

/-- **Circuits of fan-in two need `(4.56 - ε) n` gates**: the exact Gaussian coefficient is at
least `114/25`. -/
public theorem lowerBound_456 : CircuitLowerBound (114 / 25) :=
  lowerBound_gaussian.mono Gaussian.circuitCoefficient_ge_456

/-- info: 'Proofs.lowerBound_456' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerBound_456

/-- **Circuits of fan-in two below `(4 - ε) n` gates barely beat guessing** on sets with small
bias on large rectangles, by Gaussian vertex-score layouts. -/
public theorem averageCase_four : AverageCaseBound 4 := by
  have h := averageCase_of_layoutBound (by norm_num) layoutBound_one_third
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-- info: 'Proofs.averageCase_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms averageCase_four

/-- **Circuits of fan-in two below `(L - ε) n` gates barely beat guessing** on sets with small
bias on large rectangles, by median edge-score layouts, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625` is the exact Gaussian coefficient. -/
public theorem averageCase_gaussian :
    AverageCaseBound (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4))) := by
  have h := averageCase_of_layoutBound (mul_pos two_pos Gaussian.gaussianCoefficient_pos)
    layoutBound_gaussian
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/--
info: 'Proofs.averageCase_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms averageCase_gaussian

/-- **Circuits of fan-in two below `(4.56 - ε) n` gates barely beat guessing**: the exact
Gaussian coefficient is at least `114/25`. -/
public theorem averageCase_456 : AverageCaseBound (114 / 25) :=
  averageCase_gaussian.mono Gaussian.circuitCoefficient_ge_456

/-- info: 'Proofs.averageCase_456' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms averageCase_456

end Proofs
