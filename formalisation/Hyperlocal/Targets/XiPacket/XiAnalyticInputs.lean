/-
  Hyperlocal/Targets/XiPacket/XiAnalyticInputs.lean

  Analytic Inputs for Xi (Route A) — Single-file shim

  Snapshot-robust:
  * FE is theorem-level from Mathlib.
  * RC and AnalyticAt(Λ) are local shields until you wire exact lemma names.
  * Entirety of xi is proved from those shields by analytic closure.
  * Route-A quartet factorisation handoff stays as a single local axiom.
-/

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
# Analytic Inputs for Xi (Route A) — Single-file shim
-/

-- IMPORTANT: avoid name collision with your existing `Xi`.
private abbrev XiFn : ℂ → ℂ := Hyperlocal.xi

/-! ---------------------------------------------------------------------------
0. Mathlib facts / local shields
---------------------------------------------------------------------------- -/

/-- FE for completed zeta (Mathlib). -/
theorem completedRiemannZeta_FE (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  simpa using (completedRiemannZeta_one_sub (s := s))

/--
RC shield for completed zeta, in `starRingEnd` form (safe for your simp regime).

Replace later once you locate the right Mathlib lemma name.
-/
axiom completedRiemannZeta_RC' (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (completedRiemannZeta s)

/--
Analyticity shield for completed zeta.

Replace later once you pin down the `AnalyticAt` lemma name in your snapshot.
-/
axiom completedRiemannZeta_analyticAt (z : ℂ) :
    AnalyticAt ℂ completedRiemannZeta z

/-- Route-A handoff: existence of an entire quotient after factoring out the quartet. -/
axiom Xi_exists_factorisedByQuartet_entire (s : OffSeed XiFn) :
  ∃ G : ℂ → ℂ, FactorisedByQuartet XiFn s.ρ 1 G ∧ GrowthOrder.EntireFun G

/-! ---------------------------------------------------------------------------
1. Functional Equation (FE)
---------------------------------------------------------------------------- -/

/-- **FE**: `XiFn (1 - s) = XiFn s`. -/
theorem Xi_FE : Factorization.FunFE XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi]
  -- normalize `oneMinus` convention
  simp [oneMinus]
  rw [completedRiemannZeta_FE (s := s)]
  ring

/-! ---------------------------------------------------------------------------
2. Reality Condition (RC)
---------------------------------------------------------------------------- -/

/-- **RC**: `XiFn (conj s) = conj (XiFn s)` (here conj = `starRingEnd`). -/
theorem Xi_RC : FactorizationRC.FunRC XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi]
  -- rewrite only the zeta term
  rw [completedRiemannZeta_RC' (s := s)]
  -- expand ring-hom image safely (NO simp loops)
  simp only [map_mul, map_sub, map_one, mul_assoc]

/-! ---------------------------------------------------------------------------
3. Entirety
---------------------------------------------------------------------------- -/

/-- **Entirety**: `XiFn` is analytic everywhere (as used by `GrowthOrder`). -/
theorem Xi_entire : GrowthOrder.EntireFun XiFn := by
  intro z

  -- Force the goal into the exact unfolded shape of your `Hyperlocal.xi`.
  -- (This avoids definitional-parentheses mismatch entirely.)
  change AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta w) z

  have h_id  : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have h_one : AnalyticAt ℂ (fun _w : ℂ => (1 : ℂ)) z := analyticAt_const
  have h_sub : AnalyticAt ℂ (fun w : ℂ => w - (1 : ℂ)) z := h_id.sub h_one
  have h_poly : AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ))) z := h_id.mul h_sub
  have h_zeta : AnalyticAt ℂ completedRiemannZeta z :=
    completedRiemannZeta_analyticAt (z := z)

  have h_prod :
      AnalyticAt ℂ (fun w : ℂ => (w * (w - (1 : ℂ))) * completedRiemannZeta w) z :=
    h_poly.mul h_zeta

  -- Only reassociate; DO NOT rewrite `w - 1` into `w + -1`.
  simpa [mul_assoc] using h_prod

/-! ---------------------------------------------------------------------------
4. Quartet polynomial
---------------------------------------------------------------------------- -/

/-- Explicit FE/RC quartet polynomial (order 1). -/
def Rquartet (ρ : ℂ) : Polynomial ℂ :=
  (X - C ρ) * (X - C (star ρ)) * (X - C (1 - ρ)) * (X - C (1 - star ρ))

lemma Rquartet_eval_rho (ρ : ℂ) : (Rquartet ρ).eval ρ = 0 := by simp [Rquartet]
lemma Rquartet_eval_star (ρ : ℂ) : (Rquartet ρ).eval (star ρ) = 0 := by simp [Rquartet]
lemma Rquartet_eval_oneMinus (ρ : ℂ) : (Rquartet ρ).eval (1 - ρ) = 0 := by simp [Rquartet]
lemma Rquartet_eval_oneMinus_star (ρ : ℂ) : (Rquartet ρ).eval (1 - star ρ) = 0 := by simp [Rquartet]

lemma R_quartet_zeros (s : OffSeed XiFn) :
    (Rquartet s.ρ).eval s.ρ = 0 ∧
    (Rquartet s.ρ).eval (star s.ρ) = 0 ∧
    (Rquartet s.ρ).eval (1 - s.ρ) = 0 ∧
    (Rquartet s.ρ).eval (1 - star s.ρ) = 0 := by
  refine And.intro (Rquartet_eval_rho s.ρ) ?_
  refine And.intro (Rquartet_eval_star s.ρ) ?_
  refine And.intro (Rquartet_eval_oneMinus s.ρ) ?_
  exact Rquartet_eval_oneMinus_star s.ρ

/-! ---------------------------------------------------------------------------
5. Factorisation handoff
---------------------------------------------------------------------------- -/

theorem G_Xi_entire (s : OffSeed XiFn) :
    ∃ G : ℂ → ℂ, FactorisedByQuartet XiFn s.ρ 1 G ∧ GrowthOrder.EntireFun G := by
  exact Xi_exists_factorisedByQuartet_entire s

end XiPacket
end Targets
end Hyperlocal
