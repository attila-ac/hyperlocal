import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_GenericPrime
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityIm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-
  Collapse the explicit `hwpop` hypothesis in the generic-prime ell/identity lane.

  Once the generic-prime true-analytic recurrence payload is present, the missing
  upstream theorem
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0
  is now automatic, so the receiver-side all-primes theorems no longer need to
  expose `hwpop`.
-/

/--
Generic-prime real-pivot ell-out, with the explicit `hwpop` burden discharged by
the generic-prime true-analytic recurrence payload.
-/
theorem xiToeplitzEllOutAt_p_fromRecurrenceC_of_trueAnalyticPrime
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0 := by
  exact xiToeplitzEllOutAt_p_fromRecurrenceC_of_row0
    (m := m) (s := s) (p := p)
    (hroute := hroute)
    (hwpop := xiJetQuot_row0_wpAt_of_trueAnalyticPrime
      (m := m) (s := s) (p := p))

/--
Generic-prime mixed imag-pivot ell-out, with the explicit `hwpop` burden
discharged by the generic-prime true-analytic recurrence payload.
-/
theorem xiToeplitzEllOutAtImRe_p_fromRecurrenceC_of_trueAnalyticPrime
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0 := by
  exact xiToeplitzEllOutAtImRe_p_fromRecurrenceC_of_row0
    (m := m) (s := s) (p := p)
    (hroute := hroute)
    (hwpop := xiJetQuot_row0_wpAt_of_trueAnalyticPrime
      (m := m) (s := s) (p := p))

/--
Generic-prime real-pivot identity route, with the explicit `hwpop` burden
removed.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_p_of_trueAnalyticPrime
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk : kappaAt m s ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact xiToeplitzRecurrenceIdentity_atOrder_p_of_row0
    (m := m) (s := s) (p := p)
    (hroute := hroute)
    (hk := hk)
    (hwpop := xiJetQuot_row0_wpAt_of_trueAnalyticPrime
      (m := m) (s := s) (p := p))

/--
Generic-prime imag-pivot identity route, with the explicit `hwpop` burden
removed.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_im_p_of_trueAnalyticPrime
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk : kappaAtIm m s ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact xiToeplitzRecurrenceIdentity_atOrder_im_p_of_row0
    (m := m) (s := s) (p := p)
    (hroute := hroute)
    (hk := hk)
    (hwpop := xiJetQuot_row0_wpAt_of_trueAnalyticPrime
      (m := m) (s := s) (p := p))

/--
Pivot-gate generic-prime wrapper:
once the scalar Route-A gate is supplied, the now-closed all-primes receiver lane
produces `bCoeff(...,p)=0` for arbitrary prime windows without any extra `hwpop`
input.
-/
theorem xiToeplitzRecurrenceIdentity_p_of_trueAnalyticPrime
    (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  rcases (xiKappaPivotNonzero_out (s := s)) with hRe | hIm
  · rcases hRe with ⟨m, hk⟩
    exact xiToeplitzRecurrenceIdentity_atOrder_p_of_trueAnalyticPrime
      (m := m) (s := s) (p := p)
      (hroute := hroute) (hk := hk)
  · rcases hIm with ⟨m, hk⟩
    exact xiToeplitzRecurrenceIdentity_atOrder_im_p_of_trueAnalyticPrime
      (m := m) (s := s) (p := p)
      (hroute := hroute) (hk := hk)

end XiPacket
end Targets
end Hyperlocal
