/-
  Hyperlocal/Targets/XiPacket/XiAnalyticInputs.lean

  Cancellation shim + Xi_entire closure adjusted.

  Snapshot reality:
  * This Mathlib snapshot does not expose a usable “mellin commutes with conj/starRingEnd”
    lemma under any stable name (your grep confirms this).
  * Therefore we keep exactly ONE axiom as the RC hinge for Λ₀.

  Everything else (analyticity, cancellation shim, Xi_entire, quartet polynomial facts) is theorem-level.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Core
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Hyperlocal.MinimalModel
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.GrowthOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Polynomial
open scoped Topology
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization

private abbrev XiFn : ℂ → ℂ := Hyperlocal.xi
private abbrev conjEnd : ℂ →+* ℂ := starRingEnd ℂ
private def a0 : UnitAddCircle := (0 : UnitAddCircle)

-- ------------------------------------------------------------------
-- Differentiable → AnalyticAt bridge (snapshot-specific helper)
-- ------------------------------------------------------------------

private lemma eventually_of_forall'
    {α : Type} {l : Filter α} {P : α → Prop} (h : ∀ x, P x) :
    (∀ᶠ x in l, P x) := by
  have htrue : (∀ᶠ x in l, True) := by simp
  have hset : ({x : α | P x} : Set α) = {x : α | True} := by
    ext x; simp [h x]
  simpa [Filter.Eventually, hset] using htrue

/-- Λ₀ is analytic everywhere (theorem-level) in this snapshot. -/
theorem completedRiemannZeta₀_analyticAt (z : ℂ) :
    AnalyticAt ℂ completedRiemannZeta₀ z := by
  have hdiff_all : ∀ w : ℂ, DifferentiableAt ℂ completedRiemannZeta₀ w := by
    intro w
    -- available in this snapshot from `Mathlib.NumberTheory.LSeries.RiemannZeta`
    simpa using (differentiable_completedZeta₀.differentiableAt)
  have hev : ∀ᶠ w in nhds z, DifferentiableAt ℂ completedRiemannZeta₀ w :=
    eventually_of_forall' (l := nhds z) hdiff_all
  exact (analyticAt_iff_eventually_differentiableAt).2 hev

-- ------------------------------------------------------------------
-- SINGLE AXIOM LEFT: RC hinge for Λ₀
-- ------------------------------------------------------------------

/--
Reality condition (RC) hinge for `completedRiemannZeta₀` (Λ₀).

In this Mathlib snapshot, proving this axiom-free requires a bespoke conjugation-invariance proof
through the Hurwitz-even FE-pair / Mellin representation, and no packaged lemma is available.
So we keep this as the sole axiom in this file.
-/
axiom completedRiemannZeta₀_RC (s : ℂ) :
    completedRiemannZeta₀ (conjEnd s) =
      conjEnd (completedRiemannZeta₀ s)

-- ------------------------------------------------------------------
-- RC for completedRiemannZeta, derived from Λ₀ RC
-- ------------------------------------------------------------------

theorem completedRiemannZeta_RC (s : ℂ) :
    completedRiemannZeta (conjEnd s) =
      conjEnd (completedRiemannZeta s) := by
  classical
  rw [completedRiemannZeta_eq (s := (conjEnd s))]
  rw [completedRiemannZeta_eq (s := s)]
  simp [completedRiemannZeta₀_RC, conjEnd, div_eq_mul_inv,
    sub_eq_add_neg, mul_assoc, add_assoc, add_left_comm, add_comm]

-- ------------------------------------------------------------------
-- Cancellation shim (THEOREM-LEVEL): entire extension via Λ₀
-- ------------------------------------------------------------------

/--
Entire extension of the pole-cancelled product.

Normalized form: `w*(w-1)*Λ₀(w) + 1`.
(This is definitional-equal to `w*(w-1)*Λ(w)` on `w ≠ 0,1`.)
-/
def cancelledCompletedZeta (w : ℂ) : ℂ :=
  w * (w - (1 : ℂ)) * completedRiemannZeta₀ w + 1

theorem cancelledCompletedZeta_analyticAt (z : ℂ) :
    AnalyticAt ℂ cancelledCompletedZeta z := by
  have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have hconst1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
  have hsub1 : AnalyticAt ℂ (fun w : ℂ => w - (1 : ℂ)) z := by
    simpa [sub_eq_add_neg] using hid.sub hconst1
  have hΛ0 : AnalyticAt ℂ completedRiemannZeta₀ z :=
    completedRiemannZeta₀_analyticAt (z := z)
  have htermA :
      AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta₀ w) z :=
    (hid.mul hsub1).mul hΛ0
  simpa [cancelledCompletedZeta] using htermA.add analyticAt_const

/--
Valid cancellation on the punctured domain: for `w ≠ 0,1`,
`w*(w-1)*Λ(w) = w*(w-1)*Λ₀(w) + 1`.
-/
theorem cancelledCompletedZeta_eq_raw {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    w * (w - (1 : ℂ)) * completedRiemannZeta w = cancelledCompletedZeta w := by
  classical
  have h1' : (1 - w) ≠ 0 := by
    intro hw
    have hw' : w = 1 := by
      simpa [eq_comm] using (sub_eq_zero.mp hw)
    exact h1 hw'
  simp [cancelledCompletedZeta, completedRiemannZeta_eq (s := w),
    div_eq_mul_inv, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] at *
  field_simp [h0, h1, h1']
  ring

-- ------------------------------------------------------------------
-- FE / RC / Entirety for Xi
-- ------------------------------------------------------------------

theorem Xi_FE : Factorization.FunFE XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi, Hyperlocal.oneMinus]
  rw [completedRiemannZeta₀_one_sub (s := s)]
  ring

theorem Xi_RC : FactorizationRC.FunRC XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi]
  simp [conjEnd, completedRiemannZeta₀_RC, mul_assoc, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm]

theorem Xi_entire : GrowthOrder.EntireFun XiFn := by
  intro z
  have hz : AnalyticAt ℂ cancelledCompletedZeta z :=
    cancelledCompletedZeta_analyticAt (z := z)
  simpa [XiFn, Hyperlocal.xi, cancelledCompletedZeta] using hz

-- ------------------------------------------------------------------
-- Quartet polynomial (unchanged)
-- ------------------------------------------------------------------

def Rquartet (ρ : ℂ) : Polynomial ℂ :=
  (X - C ρ) *
  (X - C (star ρ)) *
  (X - C (1 - ρ)) *
  (X - C (1 - star ρ))

lemma Rquartet_eval_rho (ρ : ℂ) :
    (Rquartet ρ).eval ρ = 0 := by simp [Rquartet]

lemma Rquartet_eval_star (ρ : ℂ) :
    (Rquartet ρ).eval (star ρ) = 0 := by simp [Rquartet]

lemma Rquartet_eval_oneMinus (ρ : ℂ) :
    (Rquartet ρ).eval (1 - ρ) = 0 := by simp [Rquartet]

lemma Rquartet_eval_oneMinus_star (ρ : ℂ) :
    (Rquartet ρ).eval (1 - star ρ) = 0 := by simp [Rquartet]

end XiPacket
end Targets
end Hyperlocal
