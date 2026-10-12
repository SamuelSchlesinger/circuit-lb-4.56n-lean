/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.BoundedDegree
public import Proofs.Layouts.CubicCompression
public import Proofs.Layouts.Gaussian

/-!
# The two layout bounds

`layoutBound_one_third`: connected multigraphs of maximum degree three have layouts of width
`(1/3 + o(1)) β₁ + o(|V|)`. Gaussian vertex scores give the coefficient
`3 arccos(2√2/3)/π ≈ 0.3245` (`Proofs.layoutBound_degree`), which is at most `1/3`.

`layoutBound_gaussian` uses median edge scores and cubic compression to improve the layout
coefficient to `2p ≈ 0.2807`, with `p = (3/(2π)) arccos((1 + 2√2)/4)`.
-/

@[expose] public section

namespace Proofs

/-- **The coefficient one third.** Connected multigraphs of maximum degree three have layouts
of width `(1/3 + o(1)) β₁ + o(|V|)`. -/
theorem layoutBound_one_third : LayoutBound 3 (1 / 3) :=
  (layoutBound_degree le_rfl).mono Gaussian.degreeCoefficient_three_le

/-- **Gaussian layouts.** Connected multigraphs of maximum degree three have layouts of width
`(2p + o(1)) β₁ + o(|V|)`, where `p = (3/(2π)) arccos ((1 + 2√2)/4)`. -/
theorem layoutBound_gaussian : LayoutBound 3 (2 * Gaussian.gaussianCoefficient) :=
  LayoutBound.of_cubic Gaussian.gaussianCoefficient_pos.le Gaussian.cubicLayoutBound_gaussian

end Proofs
