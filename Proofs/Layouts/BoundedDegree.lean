/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Layouts.MultiGaussian
public import Proofs.Layouts.Compression
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian cycle-rank constants in every fixed degree

Terminal compression and Gaussian vertex ordering give the layout bound with coefficient
`A_d = (3d / (2d - 3)) · arccos (2√(d - 1) / d) / π` for every fixed `d ≥ 3`
(`layoutBound_degree`). At `d = 3` the coefficient `3 arccos (2√2/3) / π ≈ 0.3245` is at most
`1/3` (`degreeCoefficient_three_le`).
-/

@[expose] public section

namespace Proofs

namespace Gaussian

/-- The layout coefficient `A_d = (3d / (2d - 3)) · arccos (2√(d - 1) / d) / π` of terminal
compression and Gaussian vertex scores in maximum degree `d`. -/
noncomputable def degreeCoefficient (d : ℕ) : ℝ :=
  (3 * d / (2 * d - 3)) * vertexCoefficient d

/-- The limiting adjacent correlation `2√(d - 1) / d` is less than one for `d ≥ 3`. -/
theorem vertexCorrelation_lt_one {d : ℕ} (hd : 3 ≤ d) : vertexCorrelation d < 1 := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : Real.sqrt ((d : ℝ) - 1) ^ 2 = d - 1 := Real.sq_sqrt (by linarith)
  rw [vertexCorrelation, div_lt_one (by linarith)]
  nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1), sq_pos_of_pos (show (0 : ℝ) < d - 2 by linarith)]

theorem vertexCoefficient_pos {d : ℕ} (hd : 3 ≤ d) : 0 < vertexCoefficient d :=
  div_pos (Real.arccos_pos.mpr (vertexCorrelation_lt_one hd)) Real.pi_pos

theorem degreeCoefficient_pos {d : ℕ} (hd : 3 ≤ d) : 0 < degreeCoefficient d := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact mul_pos (div_pos (by linarith) (by linarith)) (vertexCoefficient_pos hd)

/-- In degree three the coefficient `3 arccos(2√2/3)/π ≈ 0.3245` is at most `1/3`, since
`cos(π/9) ≤ 2√2/3`. -/
theorem degreeCoefficient_three_le : degreeCoefficient 3 ≤ 1 / 3 := by
  have hsqrt : (141421 : ℝ) / 100000 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  set θ := Real.pi / 9 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθlo : 0.3488 ≤ θ := by rw [hθ]; linarith
  have hθhi : θ ≤ 0.35 := by rw [hθ]; linarith
  have hcos : Real.cos θ ≤ 2 * Real.sqrt 2 / 3 := by
    have hb := Real.cos_bound (x := θ) (by rw [abs_of_nonneg hθ0]; linarith)
    rw [abs_of_nonneg hθ0] at hb
    have h2 : θ ^ 2 ≥ 0.3488 ^ 2 := by gcongr
    have h4 : θ ^ 4 ≤ 0.35 ^ 4 := by gcongr
    nlinarith [(abs_le.mp hb).2]
  have harccos : Real.arccos (2 * Real.sqrt 2 / 3) ≤ θ :=
    (Real.arccos_le_arccos hcos).trans_eq (Real.arccos_cos hθ0 (by rw [hθ]; linarith))
  have hρ : vertexCorrelation 3 = 2 * Real.sqrt 2 / 3 := by norm_num [vertexCorrelation]
  unfold degreeCoefficient vertexCoefficient
  rw [hρ, mul_div_assoc', div_le_iff₀ Real.pi_pos]
  norm_num
  linarith

end Gaussian

/-- **Gaussian vertex-score layouts.** For `d ≥ 3`, connected multigraphs of maximum degree `d`
have layouts of width `(A_d + o(1)) β₁ + o(|V|)`, with `A_d = degreeCoefficient d`. -/
theorem layoutBound_degree {d : ℕ} (hd : 3 ≤ d) : LayoutBound d (Gaussian.degreeCoefficient d) := by
  intro η hη
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 3 := by linarith
  obtain ⟨N₀, hN₀⟩ := Gaussian.multigraph_vertexLayout_bound (by lia : 2 ≤ d)
    (show 0 < η / 3 by positivity)
  obtain ⟨K, hK⟩ := exists_log_le_mul_add (ε := η / d) (by positivity)
  refine ⟨d * (N₀ + 1) + d + d * K, fun V E _ _ G hG hdeg => ?_⟩
  let := Fintype.ofFinite V
  obtain ⟨Q, hQ⟩ := Multigraph.Compression.exists_terminal hdeg
  let := Fintype.ofFinite Q.External
  have hA := (Gaussian.degreeCoefficient_pos hd).le
  have hβ : 0 ≤ (Gaussian.degreeCoefficient d + η) * (G.cycleRank : ℝ) := by positivity
  obtain ⟨key, hkey, hX⟩ : ∃ key : Q.blocks → ℕ, key.Injective ∧ ∀ q,
      ((Q.multiQuotient.cut {B | key B < q}).ncard : ℝ) ≤
        (Gaussian.degreeCoefficient d + η) * G.cycleRank + d * (N₀ + 1) := by
    by_cases hbig : 2 ≤ Q.blocks.card ∧ N₀ < Q.blocks.card
    · obtain ⟨key, hkey, hcut⟩ := hN₀ Q.blocks Q.External Q.multiQuotient
        Q.multiQuotient_loopless Q.multiQuotient_maxDegreeLE
        (by rw [Fintype.card_coe]; exact hbig.2)
      refine ⟨key, hkey, fun q => ?_⟩
      -- The core has at most `3d/(2d-3) β₁` edges, hence at most `3 β₁` edges and blocks.
      have hE : (Q.External.ncard : ℝ) ≤ 3 * d / (2 * d - 3) * G.cycleRank := by
        have h := Nat.cast_le (α := ℝ).mpr
          (Multigraph.Compression.Terminal.multi_edge_bound Q hQ hG hbig.1)
        push_cast [Nat.cast_sub (by lia : 3 ≤ 2 * d)] at h
        rw [div_mul_eq_mul_div, le_div_iff₀ hden]
        linarith
      have hE3 : (Q.External.ncard : ℝ) ≤ 3 * G.cycleRank := by
        refine hE.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
        rw [div_le_iff₀ hden]
        linarith
      have hV : (Fintype.card Q.blocks : ℝ) ≤ 3 * G.cycleRank := by
        rw [Fintype.card_coe]
        exact (Nat.cast_le.mpr
          (Multigraph.Compression.Terminal.multi_blocks_le_edges Q hQ hG hbig.1)).trans hE3
      have hmain := mul_le_mul_of_nonneg_left hE (Gaussian.vertexCoefficient_pos hd).le
      have hslack := mul_le_mul_of_nonneg_left hV (show 0 ≤ η / 3 by positivity)
      have hcut := hcut q
      rw [Multigraph.card_cutFinset] at hcut
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq] at hcut
      rw [Nat.card_eq_fintype_card] at hcut
      have hN : (0 : ℝ) ≤ d * (N₀ + 1) := by positivity
      unfold Gaussian.degreeCoefficient
      linarith
    · refine ⟨fun B => Fintype.equivFin _ B, fun B B' h => (Fintype.equivFin _).injective
        (Fin.ext h), fun q => ?_⟩
      have hsmall : (Q.External.ncard : ℝ) ≤ d * (N₀ + 1) := by
        have he := Q.multiQuotient.card_edges_le Q.multiQuotient_maxDegreeLE
        rw [Nat.card_coe_set_eq, Fintype.card_coe] at he
        have hv : Q.blocks.card ≤ N₀ + 1 := by lia
        exact_mod_cast he.trans (Nat.mul_le_mul_left d hv)
      exact (Nat.cast_le.mpr (Set.ncard_le_card _)).trans (by
        rw [Nat.card_coe_set_eq]; linarith)
  obtain ⟨π, hπ⟩ := Q.exists_layout hkey hX
  refine ⟨π, fun t => ?_⟩
  have hlog := mul_le_mul_of_nonneg_left (hK (Nat.card V)) (show (0 : ℝ) ≤ d by positivity)
  have hcancel : (d : ℝ) * (η / d * Nat.card V + K) = η * Nat.card V + d * K := by
    field_simp
  rw [hcancel] at hlog
  linarith [hπ t]

end Proofs
