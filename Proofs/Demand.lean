/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Positivity

/-!
# Demand and supply at the frontier

Every lower bound proved here ends with the same comparison. On one side is the *demand* of the
problem: every layout of the graph of a circuit for it must, at some time, have a frontier of
about `n` edges, the information that must cross from the inputs read to the inputs not yet
read. On the other side is the *supply* of the layout hypothesis: the graph of a circuit of
size `s` has cycle rank about `s - n`, so it has a layout whose frontiers carry at most about
`A (s - n)` edges. Demand cannot exceed supply, so `n ≤ A (s - n)`, that is,
`s ≥ (1 + 1/A) n`.

`Proofs.eventually_lt_of_demand` makes this precise with every lower-order term in place. The
slack `η` of the layout hypothesis is chosen first, depending only on `A`, `ε`, and a constant
`κ` bounding the size of the graph; the constant `C` of the layout hypothesis and the error
`e(n) = o(n)` of the problem come afterwards.

## Main results

* `Proofs.eventually_lt_of_demand`: demand `n - o(n)` and supply `A (s - n + o(n)) + o(n)`
  force `s > (1 + 1/A - ε) n`.
* `Proofs.isLittleO_log_affine`: `log (α n + β) = o(n)`.
-/

@[expose] public section

namespace Proofs

open Filter Asymptotics

/-- `log (α n + β) = o(n)` for constants `α ≥ 0` and `β ≥ 1`. -/
theorem isLittleO_log_affine {α β : ℝ} (hα : 0 ≤ α) (hβ : 1 ≤ β) :
    (fun n : ℕ => Real.log (α * n + β)) =o[atTop] fun n => (n : ℝ) := by
  have hbound : (fun n : ℕ => Real.log (α + β) + Real.log n) =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop.add Real.isLittleO_log_id_atTop.natCast_atTop
  refine IsLittleO.of_bound fun δ hδ => ?_
  filter_upwards [hbound.bound hδ, eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hle : Real.log (α * n + β) ≤ Real.log (α + β) + Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hnonneg : 0 ≤ Real.log (α * n + β) := Real.log_nonneg (by nlinarith)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
    hle.trans ((le_abs_self _).trans hn)

/-- Changing from base `q ≥ 2` to the natural logarithm costs at most the factor
`1 / log 2 ≤ 4 + 1 / log 2`. -/
theorem logb_le_mul_log {q x : ℝ} (hq : 2 ≤ q) (hx : 1 ≤ x) :
    Real.logb q x ≤ (4 + 1 / Real.log 2) * Real.log x := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc Real.logb q x ≤ Real.log x / Real.log 2 :=
        div_le_div_of_nonneg_left h0 h2 (Real.log_le_log two_pos hq)
    _ = 1 / Real.log 2 * Real.log x := by ring
    _ ≤ (4 + 1 / Real.log 2) * Real.log x := by gcongr; linarith

/-- Every constant is eventually at most `δ n`. -/
private theorem eventually_le_mul {c δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, c ≤ δ * n := by
  filter_upwards [eventually_ge_atTop ⌈c / δ⌉₊] with n hn
  have h : c / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rwa [div_le_iff₀ hδ, mul_comm] at h

/-- The logarithm of a quantity of linear size is eventually at most `δ n`. -/
private theorem eventually_log_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) {κ : ℝ}
    (hκ : 0 ≤ κ) :
    ∀ᶠ n : ℕ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ a * n + b → κ * Real.log (v + 1) ≤ δ * n := by
  have hlog := isLittleO_log_affine (α := a) (β := b + 1) ha (by linarith)
  filter_upwards [hlog.bound (show 0 < δ / (κ + 1) by positivity)] with n hn
  intro v hv hvab
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)] at hn
  have hlog0 : 0 ≤ Real.log (v + 1) := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (v + 1) ≤ Real.log (a * n + (b + 1)) :=
    Real.log_le_log (by linarith) (by linarith)
  calc κ * Real.log (v + 1) ≤ (κ + 1) * Real.log (a * n + (b + 1)) := by nlinarith
    _ ≤ (κ + 1) * (δ / (κ + 1) * n) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hn) (by linarith)
    _ = δ * n := by rw [← mul_assoc, mul_div_cancel₀ _ (by positivity : κ + 1 ≠ 0)]

/-- **The comparison.** Let `δ = A ε / 10` and spend the slack `η` so that
`η (1/A + κ (2 + 1/A)) ≤ A ε / 2`. If the lower-order terms are at most `δ n` each, then the
demand `n ≤ w + e + κ log (v + 1)` and the supply `w ≤ (A + η) (s - n + e) + η v + C` force
`s > (1 + 1/A - ε) n`.

Indeed, if `s ≤ (1 + 1/A - ε) n`, then `v = O(n)` and chaining demand and supply gives
`n ≤ n + η (1/A + κ (2 + 1/A)) n - A ε n + 3 δ n ≤ n - A ε n / 5`. -/
private theorem lt_of_demand_supply {A η ε κ δ C n s v w e : ℝ} (hA : 0 < A) (hη : 0 < η)
    (hε : 0 < ε) (hκ : 0 ≤ κ) (hδ : δ = A * ε / 10)
    (hηB : η * (1 / A + κ * (2 + 1 / A)) ≤ A * ε / 2)
    (hn : 1 ≤ n) (hvκ : v ≤ κ * (n + s + 1))
    (hE : (A + η + 1) * |e| ≤ δ * n) (hC : |C| + η * κ ≤ δ * n)
    (hlog : v ≤ κ * (2 + 1 / A) * n + κ → κ * Real.log (v + 1) ≤ δ * n)
    (hdemand : n ≤ w + e + κ * Real.log (v + 1))
    (hsupply : w ≤ (A + η) * (s - n + e) + η * v + C) :
    (1 + 1 / A - ε) * n < s := by
  subst hδ
  by_contra! hsn
  have hεn : 0 ≤ ε * n := by positivity
  -- A small circuit gives a graph with `O(n)` vertices, so the log term is at most `δ n`.
  have hv' : v ≤ κ * (2 + 1 / A) * n + κ := by
    have : κ * (n + s + 1) ≤ κ * ((2 + 1 / A) * n + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hκ
    linarith
  have hL := hlog hv'
  -- The error term and the constants.
  have he : (A + η) * e + e ≤ (A + η + 1) * |e| := by
    have := mul_le_mul_of_nonneg_left (le_abs_self e) (by linarith : 0 ≤ A + η + 1)
    linarith
  have hCle : C ≤ |C| := le_abs_self C
  have hηv : η * v ≤ η * κ * (2 + 1 / A) * n + η * κ := by
    have := mul_le_mul_of_nonneg_left hv' hη.le
    linarith
  -- The main term, with the circuit small.
  have hmain : (A + η) * (s - n) ≤ (A + η) * ((1 / A - ε) * n) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hexp : (A + η) * ((1 / A - ε) * n) = n + η / A * n - A * ε * n - η * ε * n := by
    field_simp
    ring
  have hB : η / A * n + η * κ * (2 + 1 / A) * n ≤ A * ε / 2 * n := by
    have := mul_le_mul_of_nonneg_right hηB (by linarith : (0 : ℝ) ≤ n)
    linarith [show η * (1 / A + κ * (2 + 1 / A)) * n =
      η / A * n + η * κ * (2 + 1 / A) * n by ring]
  have hηε : 0 ≤ η * ε * n := by positivity
  have hpos : 0 < A * ε * n := by positivity
  -- Demand at most supply, term by term.
  have : n ≤ n + A * ε / 2 * n - A * ε * n + 3 * (A * ε / 10 * n) :=
    calc n ≤ w + e + κ * Real.log (v + 1) := hdemand
      _ ≤ (A + η) * (s - n + e) + η * v + C + e + κ * Real.log (v + 1) := by linarith
      _ = (A + η) * (s - n) + ((A + η) * e + e) + η * v + C + κ * Real.log (v + 1) := by ring
      _ ≤ (A + η) * ((1 / A - ε) * n) + A * ε / 10 * n +
          (η * κ * (2 + 1 / A) * n + η * κ) + |C| + A * ε / 10 * n := by linarith
      _ ≤ n + η / A * n - A * ε * n - η * ε * n + η * κ * (2 + 1 / A) * n +
          3 * (A * ε / 10 * n) := by linarith
      _ ≤ n + A * ε / 2 * n - A * ε * n + 3 * (A * ε / 10 * n) := by linarith
  linarith

/-- **Demand and supply at the frontier.** Fix `A > 0`, `ε > 0`, and a constant `κ ≥ 0`. For every
small enough slack `η > 0`, every constant `C`, and every error `e(n) = o(n)`, for all large `n`
the following holds. If a graph with `v ≤ κ (n + s + 1)` vertices has a layout of width `w`
that is

* at least the demand: `n ≤ w + e(n) + κ log (v + 1)`, and
* at most the supply: `w ≤ (A + η) (s - n + e(n)) + η v + C`,

then `s > (1 + 1/A - ε) n`.

In applications, `s` is `(r - 1)` times the number of gates of a circuit of fan-in `r`, the
supply is the layout hypothesis applied to a graph of cycle rank at most `s - n + e(n)`, and the
demand is a counting argument for the problem. The slack is chosen before the layout hypothesis
provides `C`. -/
theorem eventually_lt_of_demand {A : ℝ} (hA : 0 < A) {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η₀ > 0, ∀ η, 0 < η → η ≤ η₀ → ∀ (C : ℝ) (e : ℕ → ℝ), e =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n : ℕ in atTop, ∀ s v w : ℝ, 0 ≤ s → 0 ≤ v → v ≤ κ * (n + s + 1) →
        (n : ℝ) ≤ w + e n + κ * Real.log (v + 1) →
        w ≤ (A + η) * (s - n + e n) + η * v + C →
        (1 + 1 / A - ε) * n < s := by
  -- Spend the slack so that `η B ≤ A ε / 2`, where `B` collects the coefficients of `η n`.
  set B := 1 / A + κ * (2 + 1 / A)
  have hB : 0 ≤ B := by positivity
  refine ⟨A * ε / (2 * (B + 1)), by positivity, fun η hη hηle C e he => ?_⟩
  have hηB : η * B ≤ A * ε / 2 := by
    have : A * ε / (2 * (B + 1)) * B ≤ A * ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [mul_pos hA hε]
    exact (mul_le_mul_of_nonneg_right hηle hB).trans this
  -- Each lower-order term is eventually at most `δ n`, with `δ = A ε / 10`.
  set δ := A * ε / 10 with hδ_def
  have hδ : 0 < δ := by positivity
  filter_upwards [he.bound (show 0 < δ / (A + η + 1) by positivity),
    eventually_log_le (by positivity : 0 ≤ κ * (2 + 1 / A)) hκ hδ hκ, eventually_ge_atTop 1,
    eventually_le_mul (c := |C| + η * κ) hδ] with n hen hlogn hn1 hnC
  intro s v w hs hv hvκ hdemand hsupply
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hE : (A + η + 1) * |e n| ≤ δ * n := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hen
    have := mul_le_mul_of_nonneg_left hen (by linarith : 0 ≤ A + η + 1)
    rwa [← mul_assoc, mul_div_cancel₀ _ (by linarith : A + η + 1 ≠ 0)] at this
  exact lt_of_demand_supply hA hη hε hκ hδ_def hηB hN hvκ hE hnC (hlogn v hv) hdemand hsupply

/-- **Demand with a margin.** Below `(1 + 1/A - ε) n`, the frontier, the error, and the
logarithmic term fall short of `n` by the linear margin `A ε n / 2`: for some slack `η > 0`,
every constant `C`, and every error `e(n) = o(n)`, for all large `n`, if `s ≤ (1 + 1/A - ε) n`,
`v ≤ κ (n + s + 1)`, and `w ≤ (A + η) (s - n + e(n)) + η v + C`, then

`w + e(n) + κ log (v + 1) < (1 - A ε / 2) n`.

This is the comparison `eventually_lt_of_demand` with `ε / 2`, applied to the frontier
`w + A ε n / 2` and the gate budget `s + (A ε n / 2) / (A + η)`. -/
theorem eventually_add_lt_of_le {A : ℝ} (hA : 0 < A) {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η > 0, ∀ (C : ℝ) (e : ℕ → ℝ), e =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n : ℕ in atTop, ∀ s v w : ℝ, 0 ≤ s → 0 ≤ v → v ≤ κ * (n + s + 1) →
        s ≤ (1 + 1 / A - ε) * n → w ≤ (A + η) * (s - n + e n) + η * v + C →
        w + e n + κ * Real.log (v + 1) < (1 - A * ε / 2) * n := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA hκ (half_pos hε)
  refine ⟨η, hη, fun C e he => ?_⟩
  filter_upwards [H η hη le_rfl C e he] with n hn
  intro s v w hs hv hvκ hsn hw
  by_contra! hge
  have hAη : 0 < A + η := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Spend the margin on the gate budget.
  set δ := A * ε / 2 * n / (A + η) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδε : δ ≤ ε / 2 * n := by
    rw [hδ, div_le_iff₀ hAη]
    nlinarith [mul_nonneg (mul_nonneg hε.le hn0) hη.le]
  have hsupply : w + A * ε / 2 * n ≤ (A + η) * (s + δ - n + e n) + η * v + C := by
    have : (A + η) * δ = A * ε / 2 * n := by rw [hδ]; field_simp
    nlinarith
  have hvκ' : v ≤ κ * (n + (s + δ) + 1) := hvκ.trans (by gcongr; linarith)
  have := hn (s + δ) v (w + A * ε / 2 * n) (by positivity) hv hvκ' (by linarith) hsupply
  linarith

end Proofs
