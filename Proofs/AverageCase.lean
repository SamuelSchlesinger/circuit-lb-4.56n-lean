/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Proofs.Reduction
public import Proofs.Demand
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Average-case lower bounds

Let `S ⊆ U^n` have density within `b` of `1/2` on rectangles with both sides of size at least
`K`. A circuit splits the inputs into those it accepts and those it rejects, and each part is the
accepted set of a constraint network whose branching program is unambiguous. Peeling
(`Proofs.Network.abs_signedCount_accepted_le`) shows that on each part, too, the density of `S`
is within `b` of `1/2`, up to a residual of `(K - 1) ^ 2` times the size of the program. So the
circuit agrees with `S` on at most a `1/2 + b` fraction of the inputs plus the residual
(`agreement_le_of_layout`).
A circuit that leaves inputs carrying `K` assignments unread is handled directly
(`agreement_le_of_unread`).

Below `(1 + 1/A - ε) n` gates, the layout hypothesis makes the program exponentially smaller
than the `|U| ^ n` inputs (`Proofs.eventually_add_lt_of_le`), so the residual is an
exponentially small fraction (`averageCase_of_layoutBound`).

## Main results

* `Proofs.agreement_le`: agreement from the bias on the accepted and the rejected inputs.
* `Proofs.agreement_le_of_layout`, `Proofs.agreement_le_of_unread`: one circuit.
* `Proofs.averageCase_of_layoutBound`: the average-case claim with coefficient `1 + 1/A`.
-/

@[expose] public section

namespace Proofs

open Cslib.Circuits Set Filter Asymptotics

/-- **Agreement from bias.** If `S` has bias at most `β` on `T` and on its complement, up to
the residuals `R₁` and `R₂`, then membership in `S` and in `T` agree on at most a
`(1 + β)/2 + (R₁ + R₂)/(2 N)` fraction of the `N` inputs. -/
theorem agreement_le {ι U : Type*} [Finite ι] [Finite U] [Nonempty U] {S T : Set (ι → U)}
    {β R₁ R₂ : ℝ} (h₁ : |signedCount S T| ≤ β * T.ncard + R₁)
    (h₂ : |signedCount S Tᶜ| ≤ β * Tᶜ.ncard + R₂) :
    agreement S T ≤ (1 + β) / 2 + (R₁ + R₂) / (2 * Nat.card (ι → U)) := by
  have hN : (0 : ℝ) < Nat.card (ι → U) := by exact_mod_cast Nat.card_pos
  -- The agreeing inputs are those of `T` in `S` and those of `Tᶜ` outside `S`.
  have hagree : {x | x ∈ S ↔ x ∈ T} = (T ∩ S) ∪ (Tᶜ \ S) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
    tauto
  have hdisj : Disjoint (T ∩ S) (Tᶜ \ S) := disjoint_left.mpr fun x hx hx' => hx'.1 hx.1
  have hcard : ({x | x ∈ S ↔ x ∈ T}.ncard : ℝ) = (T ∩ S).ncard + (Tᶜ \ S).ncard := by
    rw [hagree, ncard_union_eq hdisj]
    push_cast
    ring
  have hT := signedCount_add_ncard S T
  have hTc := signedCount_add_ncard S Tᶜ
  have htotal : (T.ncard : ℝ) + Tᶜ.ncard = Nat.card (ι → U) := by
    exact_mod_cast ncard_add_ncard_compl T
  have hs₁ := le_abs_self (signedCount S T)
  have hs₂ := neg_abs_le (signedCount S Tᶜ)
  have e₁ : signedCount S T = (T ∩ S).ncard - (T \ S).ncard := rfl
  have e₂ : signedCount S Tᶜ = (Tᶜ ∩ S).ncard - (Tᶜ \ S).ncard := rfl
  have hβ : β * T.ncard + β * Tᶜ.ncard = β * Nat.card (ι → U) := by rw [← htotal]; ring
  rw [agreement, div_le_iff₀ hN, hcard]
  have hRHS : ((1 + β) / 2 + (R₁ + R₂) / (2 * Nat.card (ι → U))) * Nat.card (ι → U) =
      (1 + β) / 2 * Nat.card (ι → U) + (R₁ + R₂) / 2 := by
    field_simp
  rw [hRHS]
  linarith

/-- A count whose base-`q` logarithm is at most `(1 - μ) n` is at most an
`exp (-μ log 2 · n)` fraction of `q ^ n`, for `q ≥ 2`. -/
theorem div_pow_le_exp {q R μ : ℝ} {n : ℕ} (hq : 2 ≤ q) (hR : 0 < R) (hμ : 0 ≤ μ)
    (h : Real.logb q R ≤ (1 - μ) * n) : R / q ^ n ≤ Real.exp (-(μ * Real.log 2 * n)) := by
  have hq0 : 0 < q := by linarith
  have hlq : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq
  have hlq0 : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogR : Real.log R ≤ (1 - μ) * n * Real.log q := by
    rwa [Real.logb, div_le_iff₀ hlq0] at h
  have hexp : R / q ^ n = Real.exp (Real.log R - n * Real.log q) := by
    rw [Real.exp_sub, Real.exp_log hR, ← Real.log_pow, Real.exp_log (pow_pos hq0 n)]
  rw [hexp, Real.exp_le_exp]
  nlinarith [mul_nonneg hμ (Nat.cast_nonneg (α := ℝ) n)]

/-- `log_q (K ^ 3 (v + 1) q ^ (w + 4)) = w + 4 + 3 log_q K + log_q (v + 1)`. -/
theorem logb_residual {q K v : ℝ} (hq : 1 < q) (hK : 0 < K) (hv : 0 ≤ v) (w : ℕ) :
    Real.logb q (K ^ 3 * (v + 1) * q ^ (w + 4)) =
      w + 4 + 3 * Real.logb q K + Real.logb q (v + 1) := by
  have hq0 : 0 < q := by linarith
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
    (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq]
  push_cast
  ring

/-- Raising a threshold to at least two keeps its logarithm sublinear. -/
theorem isLittleO_logb_max_two {K : ℕ → ℕ}
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) (q : ℝ) :
    (fun n => Real.logb q (max (K n) 2 : ℕ)) =o[atTop] fun n => (n : ℝ) := by
  have hK' : (fun n => Real.log (max (K n) 2 : ℕ)) =o[atTop] fun n => (n : ℝ) := by
    refine IsBigO.trans_isLittleO (g := fun n => ‖Real.log (K n)‖ + Real.log 2) ?_
      (hK.norm_left.add (isLittleO_const_id_atTop _).natCast_atTop)
    refine IsBigO.of_bound' (Eventually.of_forall fun n => ?_)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
    have hK2 : (2 : ℝ) ≤ (max (K n) 2 : ℕ) := by exact_mod_cast le_max_right (K n) 2
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
      Real.norm_of_nonneg (by positivity)]
    rcases le_total (K n) 2 with h | h
    · rw [max_eq_right h]
      push_cast
      linarith [norm_nonneg (Real.log (K n))]
    · rw [max_eq_left h]
      linarith [Real.le_norm_self (Real.log (K n))]
  exact (hK'.const_mul_left (1 / Real.log q)).congr_left fun n => by
    simp only [Real.logb]
    ring

/-- If `1 + 2 log_q K ≤ n / 2`, then half of `n` coordinates carry at least `K` assignments:
`K ≤ q ^ ⌊n / 2⌋`. -/
theorem le_pow_half_of_logb {q K n : ℕ} (hq : 1 < q) (hK : 0 < K)
    (h : 1 + 2 * Real.logb q K ≤ (1 - 1 / 2) * n) : K ≤ q ^ (n / 2) := by
  have hn2 : (n : ℝ) ≤ 2 * (n / 2 : ℕ) + 1 := by
    exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by lia)
  have hlogb : Real.logb q K ≤ (n / 2 : ℕ) := by
    linarith [Nat.cast_nonneg (α := ℝ) (n / 2)]
  have := (Real.logb_le_iff_le_rpow (by exact_mod_cast hq) (by exact_mod_cast hK)).mp hlogb
  rw [Real.rpow_natCast] at this
  exact_mod_cast this

section Circuit

variable {U : Type} {σ : Signature} {n : ℕ} (I : Interpretation σ U) (Acc : Set U)
  (c : Circuit σ n 1)

/-- The inputs on which a circuit's output lies in `Acc` are the accepted inputs of its
constraint network. -/
theorem accepted_constraintNetwork_eval :
    (constraintNetwork I Acc c).accepted = {x | c.eval I x 0 ∈ Acc} :=
  accepted_constraintNetwork fun _ => Iff.rfl

/-- The inputs a constraint network reads do not depend on the accepted values. -/
theorem read_constraintNetwork (Acc' : Set U) :
    (constraintNetwork I Acc' c).read = (constraintNetwork I Acc c).read :=
  rfl

omit I Acc c in
/-- There are `|U| ^ n` inputs. -/
theorem card_input_eq : (Nat.card (Fin n → U) : ℝ) = (Nat.card U : ℝ) ^ n := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  push_cast
  rfl

variable [Finite U] [Nontrivial U]

/-- **A circuit that leaves many inputs unread.** If the inputs a circuit does not read carry
at least `K` assignments, it agrees with `S` on at most a `1/2 + b + |U| K ^ 2 / |U| ^ n`
fraction of the inputs. -/
theorem agreement_le_of_unread {S : Set (Fin n → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hK : 1 ≤ K)
    (hu : K ≤ Nat.card U ^ (constraintNetwork I Acc c).readᶜ.ncard) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤
      1 / 2 + b + (Nat.card U * K ^ 2 : ℕ) / (Nat.card U : ℝ) ^ n := by
  have bound (A : Set U) := hS.abs_signedCount_le_of_dependsOn hb
    (constraintNetwork I A c).dependsOn_read hK hu
  have h₁ := bound Acc
  have h₂ := bound Accᶜ
  rw [accepted_constraintNetwork_eval] at h₁ h₂
  convert agreement_le h₁ h₂ using 2
  · ring
  · rw [card_input_eq]
    ring

/-- **A circuit with a narrow layout.** Let the inputs a circuit of fan-in two does not read
carry fewer than `K` assignments, and let a layout of its constraint graph have all frontiers of
size at most `w`. Then the circuit agrees with `S` on at most a
`1/2 + b + K ^ 3 (|V| + 1) |U| ^ (w + 4) / |U| ^ n` fraction of the inputs. -/
theorem agreement_le_of_layout {S : Set (Fin n → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (hb : 0 ≤ b) (hfan : c.FanInAtMost 2)
    (hu : Nat.card U ^ (constraintNetwork I Acc c).readᶜ.ncard < K)
    (π : Layout (Compiler.Vertex c.program c.outputs)) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I Acc c).frontier π t).ncard ≤ w) :
    agreement S {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b +
      (K ^ 3 * (Nat.card (Compiler.Vertex c.program c.outputs) + 1) * Nat.card U ^ (w + 4) :
        ℕ) / (Nat.card U : ℝ) ^ n := by
  set v := Nat.card (Compiler.Vertex c.program c.outputs)
  set q := Nat.card U
  have bound (A : Set U) := (constraintNetwork I A c).abs_signedCount_accepted_le π
    (fun _ _ _ => Compiler.satisfies_unique) hb hS (w := w) (d := 3) (m := 1) hw
    (Compiler.maxDegreeLE I _ le_rfl hfan) (Compiler.ncard_readAt_le I _)
  have h₁ := bound Acc
  have h₂ := bound Accᶜ
  rw [accepted_constraintNetwork_eval] at h₁ h₂
  rw [read_constraintNetwork I Acc c Accᶜ] at h₂
  have h := agreement_le h₁ h₂
  -- The residual is at most `K^3 (v + 1) q ^ (w + 4)`.
  have hres : (K - 1) ^ 2 * (v * q ^ (w + 3 + 1) +
      q ^ (constraintNetwork I Acc c).readᶜ.ncard) ≤ K ^ 3 * (v + 1) * q ^ (w + 4) := by
    have hq1 : 1 ≤ q ^ (w + 4) := Nat.one_le_pow _ _ Nat.card_pos
    calc _ ≤ K ^ 2 * (v * K * q ^ (w + 4) + K * q ^ (w + 4)) := by
          gcongr
          · lia
          · exact Nat.le_mul_of_pos_right _ (by lia)
          · exact hu.le.trans (Nat.le_mul_of_pos_right _ hq1)
      _ = K ^ 3 * (v + 1) * q ^ (w + 4) := by ring
  have hresR : (((K - 1) ^ 2 * (v * q ^ (w + 3 + 1) +
      q ^ (constraintNetwork I Acc c).readᶜ.ncard) : ℕ) : ℝ) ≤
      ((K ^ 3 * (v + 1) * q ^ (w + 4) : ℕ) : ℝ) := by exact_mod_cast hres
  have hq : 0 < q := Nat.card_pos
  have hN : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  rw [card_input_eq] at h
  refine h.trans ?_
  have key : ∀ R R' : ℝ, R ≤ R' →
      (1 + 2 * b) / 2 + (R + R) / (2 * (q : ℝ) ^ n) ≤ 1 / 2 + b + R' / (q : ℝ) ^ n := by
    intro R R' hRR'
    have hhalf : (R + R) / (2 * (q : ℝ) ^ n) = R / (q : ℝ) ^ n := by
      field_simp
      ring
    rw [hhalf]
    linarith [div_le_div_of_nonneg_right hRR' hN.le]
  exact key _ _ hresR

/-- **A narrow layout of a circuit.** Suppose that connected multigraphs of maximum degree
three have layouts with frontiers of at most `(A + η) β₁ + η |V| + C` edges. If the inputs a
circuit of fan-in two does not read carry fewer than `K` assignments, its constraint graph has
a layout with frontiers of at most `w` edges, where
`w ≤ (A + η) (s - n + log_q K + 1) + η |V| + C` for `s` inner gates. -/
theorem exists_layout_le {A η C : ℝ} (hAη : 0 ≤ A + η)
    (hC : ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E), G.Connected →
      G.MaxDegreeLE 3 → ∃ π : Layout V, ∀ t,
        ((G.cut (π.initial t)).ncard : ℝ) ≤ (A + η) * G.cycleRank + η * Nat.card V + C)
    (hfan : c.FanInAtMost 2) {K : ℕ}
    (hu : Nat.card U ^ (constraintNetwork I Acc c).readᶜ.ncard < K) :
    ∃ (π : Layout (Compiler.Vertex c.program c.outputs)) (w : ℕ),
      (∀ t, ((constraintNetwork I Acc c).frontier π t).ncard ≤ w) ∧
      (w : ℝ) ≤ (A + η) * (c.innerSize - n + Real.logb (Nat.card U) K + 1) +
        η * Nat.card (Compiler.Vertex c.program c.outputs) + C := by
  set N := constraintNetwork I Acc c
  have hrank : (N.cycleRank : ℝ) ≤ c.innerSize - n + Real.logb (Nat.card U) K + 1 := by
    simpa using cycleRank_le (r := 2) hfan hu
  obtain ⟨π, hπ⟩ := hC _ _ N.toMultigraph (Compiler.connected I _)
    (Compiler.maxDegreeLE I _ le_rfl hfan)
  set B := (A + η) * N.cycleRank + η * Nat.card (Compiler.Vertex c.program c.outputs) + C
  have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
  refine ⟨π, ⌊B⌋₊, fun t => Nat.le_floor (hπ t), ?_⟩
  have := mul_le_mul_of_nonneg_left hrank hAη
  have := Nat.floor_le hB
  simp only [B] at this
  linarith

end Circuit

/-- **The average-case lower bound.** If subcubic graphs have layouts of width
`(A + o(1)) β₁ + o(|V|)`, then the average-case claim holds with coefficient `1 + 1/A`. -/
theorem averageCase_of_layoutBound {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A) :
    AverageCaseBound (1 + 1 / A) := by
  intro ε hε
  set μ := min (A * ε / 2) (1 / 2)
  have hμ : 0 < μ := lt_min (by positivity) (by norm_num)
  refine ⟨μ * Real.log 2, by positivity, ?_⟩
  intro U _ _ S K b hbias hK
  set q := Nat.card U
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Finite.one_lt_card : 2 ≤ q)
  -- Raise the thresholds to at least two.
  set K' : ℕ → ℕ := fun n => max (K n) 2
  have hlogb : (fun n => Real.logb q (K' n)) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_logb_max_two hK q
  -- The error of the problem, `e(n) = 4 + 3 log_q K'(n)`, and the constant `κ`.
  set e : ℕ → ℝ := fun n => 4 + 3 * Real.logb q (K' n)
  have he : e =o[atTop] fun n => (n : ℝ) :=
    (isLittleO_const_id_atTop _).natCast_atTop.add (hlogb.const_mul_left 3)
  set κ : ℝ := 4 + 1 / Real.log 2
  have hκ4 : 4 ≤ κ := by simp only [κ]; linarith [show 0 ≤ 1 / Real.log 2 by positivity]
  obtain ⟨η, hη, H⟩ := eventually_add_lt_of_le hA (by linarith : 0 ≤ κ) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 + 2 * Real.logb q (K' n) ≤ (1 - 1 / 2) * n := by
    filter_upwards [((isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop.add
      (hlogb.const_mul_left 2)).bound (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
    simp only [id, Real.norm_eq_abs, Nat.abs_cast] at hn
    linarith [le_abs_self (1 + 2 * Real.logb q (K' n))]
  filter_upwards [H C e he, hbias, hsmall] with n hn hbiasn hsmalln
  intro σ I Acc c hfan hsize
  have hK2 : 2 ≤ K' n := le_max_right _ _
  have hS : RectangleBias (S n) (K' n) (b n) := hbiasn.mono (le_max_left _ _)
  have hb : 0 ≤ b n := hS.nonneg (by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact le_pow_half_of_logb Finite.one_lt_card (by lia) hsmalln)
  have hexp_mono : ∀ μ', μ ≤ μ' →
      Real.exp (-(μ' * Real.log 2 * n)) ≤ Real.exp (-(μ * Real.log 2 * n)) := fun μ' h =>
    Real.exp_le_exp.mpr (by
      nlinarith [mul_nonneg (Real.log_nonneg one_le_two) (Nat.cast_nonneg (α := ℝ) n)])
  have hq0 : 0 < q := Nat.card_pos
  by_cases hu : K' n ≤ q ^ (constraintNetwork I Acc c).readᶜ.ncard
  · -- Many unread inputs: the residual is `q K'^2`.
    have hlog : Real.logb q ((q * K' n ^ 2 : ℕ) : ℝ) ≤ (1 - 1 / 2) * n := by
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by linarith)]
      exact hsmalln
    linarith [agreement_le_of_unread I Acc c hS hb (by lia) hu,
      div_pow_le_exp hq2 (by positivity) (by norm_num) hlog, hexp_mono _ (min_le_right _ _)]
  · -- Few unread inputs: a narrow layout, whose residual is exponentially small.
    push Not at hu
    obtain ⟨π, w, hw, hwle⟩ := exists_layout_le I Acc c (by linarith) hC hfan hu
    set v := Nat.card (Compiler.Vertex c.program c.outputs)
    have hlogK : 0 ≤ Real.logb q (K' n) :=
      Real.logb_nonneg (by linarith) (by exact_mod_cast (show 1 ≤ K' n by lia))
    have hsupply : (w : ℝ) ≤ (A + η) * (c.innerSize - n + e n) + η * v + C := by
      have := mul_le_mul_of_nonneg_left (show c.innerSize - n + Real.logb q (K' n) + 1 ≤
        c.innerSize - n + e n by simp only [e]; linarith) (by linarith : 0 ≤ A + η)
      linarith
    have hvκ : (v : ℝ) ≤ κ * (n + c.innerSize + 1) := by
      have hV : v ≤ 2 * 2 * c.innerSize + 3 := by
        simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
      have : (v : ℝ) ≤ 4 * c.innerSize + 3 := by exact_mod_cast hV
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) c.innerSize]
    have hmargin := hn c.innerSize v w (Nat.cast_nonneg _) (Nat.cast_nonneg _) hvκ hsize hsupply
    have hlog : Real.logb q ((K' n ^ 3 * (v + 1) * q ^ (w + 4) : ℕ) : ℝ) ≤
        (1 - A * ε / 2) * n := by
      push_cast
      rw [logb_residual (by linarith) (by positivity) (Nat.cast_nonneg _)]
      have := logb_le_mul_log hq2 (show (1 : ℝ) ≤ v + 1 by linarith [Nat.cast_nonneg (α := ℝ) v])
      simp only [e] at hmargin
      linarith
    linarith [agreement_le_of_layout I Acc c hS hb hfan hu π hw,
      div_pow_le_exp hq2 (by positivity) (by positivity) hlog, hexp_mono _ (min_le_left _ _)]

end Proofs
