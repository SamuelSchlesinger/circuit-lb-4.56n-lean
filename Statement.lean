/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n s : ℕ}

/-- The inner gates of a program are its gates of positive arity. Gates of arity zero
represent constants. -/
def Program.innerGates (p : Program σ n s) : Finset (Fin s) :=
  Finset.univ.filter fun g : Fin s => σ.Arity (p.lines g).op ≠ 0

/-- The number of positive-arity gates in a circuit; nullary constant gates are excluded. -/
def Circuit.innerSize {m : ℕ} (c : Circuit σ n m) : ℕ :=
  c.program.innerGates.card

end Cslib.Circuits

namespace Proofs

open Cslib.Circuits Filter Asymptotics

section Rectangles

variable {ι U : Type*}

/-- A rectangle with sides `A` and `B` for the cut `X` of the space of coordinates: those inputs
whose restriction to `X` lies in `A` and whose restriction to the complement of `X` lies in `B`. -/
def rectangle (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) : Set (ι → U) :=
  {x | X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B}

/-- A set of inputs `S` is `K`-rectangle-free when every rectangle inside `S`, for every cut
`X`, has a side with fewer than `K` elements. -/
def RectangleFree (S : Set (ι → U)) (K : ℕ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
    rectangle X A B ⊆ S → A.encard < K ∨ B.encard < K

/-- A set of inputs `S` has bias at most `b` on large rectangles when, on every rectangle `R`
with both sides of size at least `K`, for every cut, the density of `S` is within `b` of `1/2`:
`| |R ∩ S| - |R| / 2 | ≤ b |R|`. -/
def RectangleBias (S : Set (ι → U)) (K : ℕ) (b : ℝ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)), K ≤ A.ncard → K ≤ B.ncard →
    |((rectangle X A B ∩ S).ncard : ℝ) - (rectangle X A B).ncard / 2| ≤
      b * (rectangle X A B).ncard

/-- The fraction of inputs on which membership in `S` and membership in `T` agree. -/
noncomputable def agreement (S T : Set (ι → U)) : ℝ :=
  ({x | x ∈ S ↔ x ∈ T}.ncard : ℝ) / Nat.card (ι → U)

end Rectangles

/-- A circuit with one output decides a set `S`, accepting the values in `Acc`, when
an input is in `S` if and only when the output of the circuit lies in `Acc`. -/
def Decides {U : Type*} {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (S : Set (Fin n → U)) : Prop :=
  ∀ x, x ∈ S ↔ c.eval I x 0 ∈ Acc

/-- **The worst case claim:** Let `U` be a finite alphabet with at least two symbols, and let
`S n ⊆ U^n` be `K n`-rectangle-free, with `log K n = o(n)` and
`log |S n| = n log |U| - o(n)`. Then for every `ε > 0` and all large `n`, every circuit of
fan-in at most two that decides `S n`, over any basis on `U`, has more than `(L - ε) n` gates
of positive arity. -/
def CircuitLowerBound (L : ℝ) : Prop :=
  ∀ (U : Type) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ),
    (∀ᶠ n in atTop, RectangleFree (S n) (K n)) →
    (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
    (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop] (fun n => (n : ℝ)) →
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
        (L - ε) * n < c.innerSize

/-- **The average-case claim:** For every `ε > 0`, there is a uniform `γ > 0` such that the
following holds for every finite alphabet `U` with at least two symbols. Let `S n ⊆ U^n` have
density within `b n` of `1/2` on every rectangle with both sides of size at least `K n`, where
`log K n = o(n)`. Then for all large `n`, every circuit of fan-in at most two with at most
`(L - ε) n` gates of positive arity, over any basis on `U` and accepting any set of values,
agrees with `S n` on at most a `1/2 + b n + exp (-γ n)` fraction of inputs. -/
def AverageCaseBound (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ γ > 0,
  ∀ (U : Type) [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ) (b : ℕ → ℝ),
    (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
    (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ U)
      (Acc : Set U) (c : Circuit σ n 1), c.FanInAtMost 2 → (c.innerSize : ℝ) ≤ (L - ε) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n))

end Proofs
