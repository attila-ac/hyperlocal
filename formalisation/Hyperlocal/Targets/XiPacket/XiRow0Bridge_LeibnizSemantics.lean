/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_LeibnizSemantics.lean

  Leibniz/binomial (order-2) jet semantics for Route-A factorisation.

  This file deliberately keeps the *analytic* obligations explicit:
  we do NOT try to prove polynomial-entire/differentiable facts about `Rρk` here,
  because the lemma names differ across Mathlib snapshots and your repo already
  has dedicated analytic input files.

  What this file *does* provide:

  * a clean Prop boundary `JetLeibnizAt` matching raw-derivative Leibniz rules;
  * a theorem `jetLeibnizAt_of_factorised` that discharges the Leibniz equations
    from:
      - the Route-A factorisation equality (as functions),
      - a jet witness for `G` at `z`,
      - differentiability assumptions (taken as inputs; you can feed them from
        `XiAnalyticInputs` / `FactorizationGofSAnalytic` later).

  IMPORTANT (Mathlib snapshot detail):
  In your environment, `Differentiable ℂ f` is definitionaly `∀ x, DifferentiableAt ℂ f x`,
  so `hR t` already has type `DifferentiableAt ℂ (Rfun s) t` (an `∃ f', HasFDerivAt ...`),
  and there is NO `.differentiableAt` field to project. Use `hR t` directly.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Mathlib.Tactic
import Hyperlocal.Targets.XiPacket.XiJet3Defs


set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Polynomial
open scoped BigOperators


/-- The minimal-model quartet factor as a scalar function. -/
def Rfun (s : OffSeed Xi) : ℂ → ℂ :=
  fun t => (Hyperlocal.Factorization.Rρk s.ρ 1).eval t

/--
Order-2 Leibniz (binomial) jet semantics at a center `z` for a jet window `w`.

This is the *raw derivative* statement induced by `Xi = Rfun * G`.
-/
def JetLeibnizAt (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    -- order 0
    Xi z = (Rfun s) z * (w 0) ∧
    -- order 1
    deriv Xi z = deriv (Rfun s) z * (w 0) + (Rfun s) z * (w 1) ∧
    -- order 2
    deriv (deriv Xi) z =
      deriv (deriv (Rfun s)) z * (w 0)
        + (2 : ℂ) * (deriv (Rfun s) z) * (w 1)
        + (Rfun s) z * (w 2)

/-! ### Core analytic discharge: factorisation ⇒ Leibniz jet semantics -/

/-- Helper: rewrite `Xi` as `Rfun s * G` as an equality of functions. -/
private lemma Xi_eq_RmulG (s : OffSeed Xi) {G : ℂ → ℂ}
    (hfac : Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G) :
    Xi = fun t => (Rfun s) t * G t := by
  funext t
  simpa [Rfun] using hfac t

/--
Factorisation + a jet witness gives the Leibniz jet equations up to order 2.

We take the differentiability inputs as *explicit assumptions* (delivered by your
analytic layer), and we keep the algebra here.
-/
theorem jetLeibnizAt_of_factorised
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (G : ℂ → ℂ)
    (hfac : Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G)
    (hjet : IsJet3At G z w)
    -- we need global differentiability to form the `funext` lemma for `deriv (R*G)`
    (hR  : Differentiable ℂ (Rfun s))
    (hG  : Differentiable ℂ G)
    (hR' : Differentiable ℂ (fun t => deriv (Rfun s) t))
    (hG' : Differentiable ℂ (fun t => deriv G t)) :
    (Xi z = (Rfun s) z * (w 0)) ∧
    (deriv Xi z = deriv (Rfun s) z * (w 0) + (Rfun s) z * (w 1)) ∧
    (deriv (deriv Xi) z =
      deriv (deriv (Rfun s)) z * (w 0)
        + (2 : ℂ) * (deriv (Rfun s) z) * (w 1)
        + (Rfun s) z * (w 2)) := by
  classical
  rcases hjet with ⟨hw0, hw1, hw2⟩
  have hXi : Xi = fun t => (Rfun s) t * G t := Xi_eq_RmulG s hfac

  have hderiv_mul_fun :
      deriv (fun t => (Rfun s) t * G t)
        = fun t => deriv (Rfun s) t * G t + (Rfun s) t * deriv G t := by
    funext t
    have hRt : DifferentiableAt ℂ (Rfun s) t := hR t
    have hGt : DifferentiableAt ℂ G t := hG t
    simpa using (deriv_mul (c := Rfun s) (d := G) (x := t) hRt hGt)

  have h0' : Xi z = (Rfun s) z * (w 0) := by
    have : Xi z = (Rfun s) z * G z := by
      simpa [hXi]
    simpa [hw0] using this

  have h1' :
      deriv Xi z = deriv (Rfun s) z * (w 0) + (Rfun s) z * (w 1) := by
    have : deriv Xi z = deriv (Rfun s) z * G z + (Rfun s) z * deriv G z := by
      calc
        deriv Xi z
            = deriv (fun t => (Rfun s) t * G t) z := by
                simpa [hXi]
        _   = (fun t => deriv (Rfun s) t * G t + (Rfun s) t * deriv G t) z := by
                simpa [hderiv_mul_fun]
        _   = deriv (Rfun s) z * G z + (Rfun s) z * deriv G z := rfl
    simpa [hw0, hw1] using this

  have h2raw :
      deriv (deriv Xi) z =
        deriv (deriv (Rfun s)) z * G z
          + (deriv (Rfun s) z) * (deriv G z)
          + (deriv (Rfun s) z) * (deriv G z)
          + (Rfun s) z * (deriv (deriv G) z) := by
    have hderivXi_fun :
        deriv Xi = fun t => deriv (Rfun s) t * G t + (Rfun s) t * deriv G t := by
      funext t
      calc
        deriv Xi t
            = deriv (fun u => (Rfun s) u * G u) t := by
                simpa [hXi]
        _   = (fun u => deriv (Rfun s) u * G u + (Rfun s) u * deriv G u) t := by
                simpa [hderiv_mul_fun]
        _   = deriv (Rfun s) t * G t + (Rfun s) t * deriv G t := rfl

    have hA :
        deriv (fun t => deriv (Rfun s) t * G t) z
          = deriv (deriv (Rfun s)) z * G z + deriv (Rfun s) z * deriv G z := by
      have hRz' : DifferentiableAt ℂ (fun t => deriv (Rfun s) t) z := hR' z
      have hGz  : DifferentiableAt ℂ G z := hG z
      simpa using (deriv_mul (c := fun t => deriv (Rfun s) t) (d := G) (x := z) hRz' hGz)

    have hB :
        deriv (fun t => (Rfun s) t * deriv G t) z
          = deriv (Rfun s) z * deriv G z + (Rfun s) z * deriv (deriv G) z := by
      have hRz : DifferentiableAt ℂ (Rfun s) z := hR z
      have hGz' : DifferentiableAt ℂ (fun t => deriv G t) z := hG' z
      simpa using (deriv_mul (c := Rfun s) (d := fun t => deriv G t) (x := z) hRz hGz')

    have hSum1 : DifferentiableAt ℂ (fun t => deriv (Rfun s) t * G t) z := by
      exact (hR' z).mul (hG z)
    have hSum2 : DifferentiableAt ℂ (fun t => (Rfun s) t * deriv G t) z := by
      exact (hR z).mul (hG' z)

    calc
      deriv (deriv Xi) z
          = deriv (fun t => deriv (Rfun s) t * G t + (Rfun s) t * deriv G t) z := by
              simpa [hderivXi_fun]
      _   = deriv (fun t => deriv (Rfun s) t * G t) z
              + deriv (fun t => (Rfun s) t * deriv G t) z := by
              simpa using
                (deriv_add (f := fun t => deriv (Rfun s) t * G t)
                           (g := fun t => (Rfun s) t * deriv G t)
                           (x := z) hSum1 hSum2)
      _   =
            (deriv (deriv (Rfun s)) z * G z + deriv (Rfun s) z * deriv G z)
            +
            (deriv (Rfun s) z * deriv G z + (Rfun s) z * deriv (deriv G) z) := by
              simp [hA, hB, add_assoc, add_left_comm, add_comm]
      _   =
        deriv (deriv (Rfun s)) z * G z
          + (deriv (Rfun s) z) * (deriv G z)
          + (deriv (Rfun s) z) * (deriv G z)
          + (Rfun s) z * (deriv (deriv G) z) := by
            ring_nf

  have h2' :
      deriv (deriv Xi) z =
        deriv (deriv (Rfun s)) z * (w 0)
          + (2 : ℂ) * (deriv (Rfun s) z) * (w 1)
          + (Rfun s) z * (w 2) := by
    have h2w :
        deriv (deriv Xi) z =
          deriv (deriv (Rfun s)) z * (w 0)
            + (deriv (Rfun s) z) * (w 1)
            + (deriv (Rfun s) z) * (w 1)
            + (Rfun s) z * (w 2) := by
      simpa [hw0, hw1, hw2] using h2raw
    have hring :
        (deriv (deriv (Rfun s)) z * (w 0)
            + (deriv (Rfun s) z) * (w 1)
            + (deriv (Rfun s) z) * (w 1)
            + (Rfun s) z * (w 2))
          =
        (deriv (deriv (Rfun s)) z * (w 0)
            + (2 : ℂ) * (deriv (Rfun s) z) * (w 1)
            + (Rfun s) z * (w 2)) := by
      ring
    exact by
      simpa [add_assoc] using Eq.trans h2w hring

  exact ⟨h0', ⟨h1', h2'⟩⟩

theorem jetLeibnizAt_from_RouteA
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (hjet :
      ∃ G : ℂ → ℂ,
        Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
        IsJet3At G z w ∧
        Differentiable ℂ (Rfun s) ∧
        Differentiable ℂ G ∧
        Differentiable ℂ (fun t => deriv (Rfun s) t) ∧
        Differentiable ℂ (fun t => deriv G t)) :
    JetLeibnizAt s z w := by
  rcases hjet with ⟨G, hfac, hJ, hR, hG, hR', hG'⟩
  refine ⟨G, hfac, hJ, ?_, ?_, ?_⟩
  · exact (jetLeibnizAt_of_factorised s z w G hfac hJ hR hG hR' hG').1
  · exact (jetLeibnizAt_of_factorised s z w G hfac hJ hR hG hR' hG').2.1
  · exact (jetLeibnizAt_of_factorised s z w G hfac hJ hR hG hR' hG').2.2

end XiPacket
end Targets
end Hyperlocal
