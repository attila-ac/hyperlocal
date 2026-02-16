import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Core
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Hyperlocal.MinimalModel
import Hyperlocal.FactorizationGofSEntire
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.GrowthOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Polynomial
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization

/-!
  # Analytic Inputs for Xi (Route A)

  This file provides the analytic assumptions/inputs about the target `Xi`
  required by the Route-A recurrence extraction.
-/

/-! ---------------------------------------------------------------------------
  0. Local "name-drift shields" (replace by theorems once names are confirmed)
---------------------------------------------------------------------------- -/

/-- FE for the completed zeta: replace by the actual Mathlib lemma you have. -/
axiom completedRiemannZeta_FE (s : ℂ) :
  completedRiemannZeta (1 - s) = completedRiemannZeta s

/-- RC for the completed zeta: replace by the actual Mathlib lemma you have. -/
axiom completedRiemannZeta_RC (s : ℂ) :
  completedRiemannZeta (star s) = star (completedRiemannZeta s)

/-- Analyticity of the completed zeta: replace by the actual Mathlib lemma you have. -/
axiom completedRiemannZeta_analyticAt (z : ℂ) :
  AnalyticAt ℂ completedRiemannZeta z

/-- Route-A handoff: existence of an entire quotient after factoring out the quartet. -/
axiom Xi_exists_factorisedByQuartet_entire (s : OffSeed Xi) :
  ∃ G : ℂ → ℂ, FactorisedByQuartet Xi s.ρ 1 G ∧ GrowthOrder.EntireFun G

/-! ## 1. Functional Equation (FE) -/

/--
**FE**: `Xi (1 - s) = Xi s`.
-/
theorem Xi_FE : Factorization.FunFE Xi := by
  intro s
  dsimp [Xi, xi, oneMinus]
  rw [completedRiemannZeta_FE s]
  generalize completedRiemannZeta s = Z
  ring

/-! ## 2. Reality Condition (RC) -/

/--
**RC**: `Xi (conj s) = conj (Xi s)`.
-/
theorem Xi_RC : FactorizationRC.FunRC Xi := by
  intro s
  dsimp [Xi, xi]

  -- Explicitly align syntax for the axiom rewrite
  change star s * (star s - 1) * completedRiemannZeta (star s) = star (s * (s - 1) * completedRiemannZeta s)

  -- Rewrite zeta term
  rw [completedRiemannZeta_RC s]

  -- Trick: Convert the RHS `star (...)` to `starRingEnd ℂ (...)`
  -- This allows us to use `map_mul`, `map_sub`, `map_one` which only work on RingHoms.
  rw [←starRingEnd_apply (s * (s - 1) * completedRiemannZeta s)]

  -- Now expand the structure using the map lemmas
  simp only [map_mul, map_sub, map_one]

  -- Convert back from starRingEnd to star for the final match
  simp only [starRingEnd_apply]

/-! ## 3. Entirety -/

/-- **Entirety**: `Xi` is analytic everywhere. -/
theorem Xi_entire : GrowthOrder.EntireFun Xi := by
  intro z
  dsimp [Xi, xi]

  -- Atomic analyticities with EXPLICIT types
  have h_s : AnalyticAt ℂ (fun w => w) z := analyticAt_id
  have h_const : AnalyticAt ℂ (fun w => (1 : ℂ)) z := analyticAt_const
  have h_sub : AnalyticAt ℂ (fun w => w - (1 : ℂ)) z := h_s.sub h_const
  have h_poly : AnalyticAt ℂ (fun w => w * (w - (1 : ℂ))) z := h_s.mul h_sub
  have h_zeta : AnalyticAt ℂ completedRiemannZeta z := completedRiemannZeta_analyticAt z

  -- Combine
  have h_prod : AnalyticAt ℂ (fun w => (w * (w - (1 : ℂ))) * completedRiemannZeta w) z :=
    h_poly.mul h_zeta

  -- Use 'convert' to match up to associativity
  convert h_prod using 1

/-! ---------------------------------------------------------------------------
  4. Quartet polynomial: defined explicitly here
---------------------------------------------------------------------------- -/

/--
The explicit FE/RC quartet polynomial (order 1): roots are
`ρ`, `conj ρ`, `1-ρ`, `1-conj ρ`.
-/
def Rquartet (ρ : ℂ) : Polynomial ℂ :=
  (X - C ρ) * (X - C (star ρ)) * (X - C (1 - ρ)) * (X - C (1 - star ρ))

lemma Rquartet_eval_rho (ρ : ℂ) : (Rquartet ρ).eval ρ = 0 := by simp [Rquartet]
lemma Rquartet_eval_star (ρ : ℂ) : (Rquartet ρ).eval (star ρ) = 0 := by simp [Rquartet]
lemma Rquartet_eval_oneMinus (ρ : ℂ) : (Rquartet ρ).eval (1 - ρ) = 0 := by simp [Rquartet]
lemma Rquartet_eval_oneMinus_star (ρ : ℂ) : (Rquartet ρ).eval (1 - star ρ) = 0 := by simp [Rquartet]

/-- Packaged quartet-root statement. -/
lemma R_quartet_zeros (s : OffSeed Xi) :
    (Rquartet s.ρ).eval s.ρ = 0 ∧
    (Rquartet s.ρ).eval (star s.ρ) = 0 ∧
    (Rquartet s.ρ).eval (1 - s.ρ) = 0 ∧
    (Rquartet s.ρ).eval (1 - star s.ρ) = 0 := by
  refine And.intro (Rquartet_eval_rho s.ρ) ?_
  refine And.intro (Rquartet_eval_star s.ρ) ?_
  refine And.intro (Rquartet_eval_oneMinus s.ρ) ?_
  exact Rquartet_eval_oneMinus_star s.ρ

/-! ## 5. Factorisation and entire quotient G (Route A handoff) -/

/--
**Crucial Route-A handoff**: factor out the quartet polynomial and obtain an entire `G`.
Uses the local axiom `Xi_exists_factorisedByQuartet_entire`.
-/
theorem G_Xi_entire (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ, FactorisedByQuartet Xi s.ρ 1 G ∧ GrowthOrder.EntireFun G := by
  exact Xi_exists_factorisedByQuartet_entire s

end XiPacket
end Targets
end Hyperlocal
