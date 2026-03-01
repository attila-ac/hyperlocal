/-
  Hyperlocal/Targets/XiPacket/XiAnalyticInputs.lean

  Analytic Inputs for Xi (Route A)

  A1 stop-the-bleeding (snapshot-safe):
  * RC for Λ and Xi are theorem-level from the single Λ₀ RC hinge.
  * Entirety of Xi is reduced to analyticity of the pole-cancelled function
        z ↦ z * (z - 1) * completedRiemannZeta z.
  * We additionally prove theorem-level analyticity of Λ₀ from differentiability,
    via `analyticAt_iff_eventually_differentiableAt` (CauchyIntegral bridge).

  Remaining axioms:
      - completedRiemannZeta₀_RC
      - cancelled_completedZeta_analyticAt
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
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

/-- Avoid name collision with your existing `Xi`. -/
private abbrev XiFn : ℂ → ℂ := Hyperlocal.xi

/-- Conjugation as a ring endomorphism. -/
private abbrev conjEnd : ℂ →+* ℂ := starRingEnd ℂ

/-- The `a = 0` parameter lives in `UnitAddCircle`. (Kept for local symmetry proofs if needed.) -/
private def a0 : UnitAddCircle := (0 : UnitAddCircle)

-- ------------------------------------------------------------------
-- Differentiable → AnalyticAt bridge (snapshot-specific helper)
-- ------------------------------------------------------------------

/--
Replacement for `Filter.eventually_of_forall` (missing in your environment).

We avoid using `Filter.univ_mem` directly (it `simp`s to `True` in this snapshot),
and instead derive `∀ᶠ x in l, True` by `simp`, then rewrite.
-/
private lemma eventually_of_forall'
    {α : Type} {l : Filter α} {P : α → Prop} (h : ∀ x, P x) :
    (∀ᶠ x in l, P x) := by
  -- `Eventually True` is always available by simp
  have htrue : (∀ᶠ x in l, True) := by simp
  -- rewrite `{x | P x}` to `{x | True}` using the pointwise proof `h`
  have hset : ({x : α | P x} : Set α) = {x : α | True} := by
    ext x; simp [h x]
  -- now transport the eventuality statement
  simpa [Filter.Eventually, hset] using htrue

/--
In this snapshot: `DifferentiableAt` on a neighborhood is equivalent to `AnalyticAt`,
via `analyticAt_iff_eventually_differentiableAt`.
In particular, `completedRiemannZeta₀` is analytic everywhere (theorem-level).
-/
theorem completedRiemannZeta₀_analyticAt (z : ℂ) :
    AnalyticAt ℂ completedRiemannZeta₀ z := by
  have hdiff_all : ∀ w : ℂ, DifferentiableAt ℂ completedRiemannZeta₀ w := by
    intro w
    simpa using (differentiable_completedZeta₀.differentiableAt)
  have hev : ∀ᶠ w in nhds z, DifferentiableAt ℂ completedRiemannZeta₀ w :=
    eventually_of_forall' (l := nhds z) hdiff_all
  exact (analyticAt_iff_eventually_differentiableAt).2 hev

-- ------------------------------------------------------------------
-- RC for Λ₀ and Λ (Λ₀ hinge kept as axiom)
-- ------------------------------------------------------------------

/-- FE for completed zeta (Mathlib). -/
theorem completedRiemannZeta_FE (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  simpa using (completedRiemannZeta_one_sub (s := s))

/--
Remaining RC hinge (axiom): RC for `completedRiemannZeta₀`.
-/
axiom completedRiemannZeta₀_RC (s : ℂ) :
    completedRiemannZeta₀ (conjEnd s) =
      conjEnd (completedRiemannZeta₀ s)

/-- RC for `completedRiemannZeta`, derived from `completedRiemannZeta_eq` and Λ₀ RC. -/
theorem completedRiemannZeta_RC (s : ℂ) :
    completedRiemannZeta (conjEnd s) =
      conjEnd (completedRiemannZeta s) := by
  classical
  rw [completedRiemannZeta_eq (s := (conjEnd s))]
  rw [completedRiemannZeta_eq (s := s)]
  simp [completedRiemannZeta₀_RC, conjEnd, div_eq_mul_inv,
    sub_eq_add_neg, mul_assoc, add_assoc, add_left_comm, add_comm]

-- ------------------------------------------------------------------
-- FE / RC / Entirety for Xi
-- ------------------------------------------------------------------

/-- **FE**: `XiFn (1 - s) = XiFn s`. -/
theorem Xi_FE : Factorization.FunFE XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi]
  simp [Hyperlocal.oneMinus]
  rw [completedRiemannZeta_FE (s := s)]
  ring

/-- **RC**: `XiFn (conj s) = conj (XiFn s)`. -/
theorem Xi_RC : FactorizationRC.FunRC XiFn := by
  intro s
  dsimp [XiFn, Hyperlocal.xi]
  rw [completedRiemannZeta_RC (s := s)]
  simp [conjEnd, mul_assoc, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-
Temporary analytic hinge:

Analyticity of the pole-cancelled Λ everywhere.
Still missing as a named lemma in Mathlib v4.23.0-rc2, so it stays an axiom for now.
-/
axiom cancelled_completedZeta_analyticAt (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta w) z

/--
Rewrite lemma: make the definitional shape of `Hyperlocal.xi` explicit.
-/
theorem xi_eq_cancelled :
    XiFn = (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta w) := by
  rfl

/-- Entirety of Xi (as used by `GrowthOrder`). -/
theorem Xi_entire : GrowthOrder.EntireFun XiFn := by
  intro z
  have hz :
      AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta w) z :=
    cancelled_completedZeta_analyticAt (z := z)
  simpa [xi_eq_cancelled] using hz

-- ------------------------------------------------------------------
-- Quartet polynomial (unchanged, kept local)
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
