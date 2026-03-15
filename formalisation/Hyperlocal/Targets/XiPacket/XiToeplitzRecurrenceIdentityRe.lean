/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentityRe.lean

  Real-pivot half only:
    * generic all-primes eliminator from an explicit ell-zero hypothesis
    * order-m theorem consuming `kappaAt m s ≠ 0`
    * order-0 wrapper in `{2,3}` API form

  2026-03-13 honest post-axiom state:
  * `xiToeplitzEllOutAt_fromRecurrenceC` is now theorem-gated
  * therefore these exported theorem surfaces can no longer remain assumption-free
  * they must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
      [RouteAWcScalarProvider]

  plus the explicit Route-A scalar-zero payload required by the `wc` branch.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder_GenericPrime
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem
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

/--
Generic real-pivot eliminator:

if the real-pivot ell-functional vanishes on `wpAt m s p`, then `bCoeff(...,p)=0`
provided `kappaAt m s ≠ 0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_p_of_hell
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    (hk : kappaAt m s ≠ 0)
    (hEll :
      Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  have hmul :
      bCoeff (σ s) (t s) (p : ℝ) *
          kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
    have h := hEll
    rw [ell_wpAt_eq_b_mul_kappa (m := m) (s := s) (p := p)] at h
    simpa using h

  have hmul' : bCoeff (σ s) (t s) (p : ℝ) * kappaAt m s = 0 := by
    simpa [kappaAt, mul_assoc] using hmul

  exact (mul_eq_zero.mp hmul').resolve_right hk

/--
Identity route at order `m` (real pivot):

ell-out at order `m` + `kappaAt m s ≠ 0` ⇒ `bCoeff(2)=0 ∧ bCoeff(3)=0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk : kappaAt m s ≠ 0) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 ∧
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  classical

  have hell : XiToeplitzEllOutAt m s :=
    xiToeplitzEllOutAt_fromRecurrenceC (m := m) (s := s) (hroute := hroute)

  refine ⟨?_, ?_⟩
  · simpa [wp2At] using
      (xiToeplitzRecurrenceIdentity_atOrder_p_of_hell
        (m := m) (s := s) (p := 2) (hk := hk) (hEll := hell.hell2))
  · simpa [wp3At] using
      (xiToeplitzRecurrenceIdentity_atOrder_p_of_hell
        (m := m) (s := s) (p := 3) (hk := hk) (hEll := hell.hell3))

/--
Order-0 wrapper in the `{2,3}` API form, consuming only `kappaAt 0 s ≠ 0`.
-/
theorem xiToeplitzRecurrenceIdentity_p_of_kappaAt0
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk0 : kappaAt (0 : ℕ) s ≠ 0)
    (p : ℝ) (hp : p = (2 : ℝ) ∨ p = (3 : ℝ)) :
    bCoeff (σ s) (t s) p = 0 := by
  classical
  have hb := xiToeplitzRecurrenceIdentity_atOrder (m := 0) (s := s) (hroute := hroute) hk0
  rcases hp with rfl | rfl
  · exact hb.1
  · exact hb.2

/--
Generic-prime real-pivot theorem surface.

This is the honest next W1 receiver-side theorem:
once the upstream lane can provide row-0 zero for `wpAt m s p`, the real-pivot
identity immediately yields `bCoeff(...,p)=0`.
-/
theorem xiToeplitzRecurrenceIdentity_atOrder_p_of_row0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hk : kappaAt m s ≠ 0)
    (hwpop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact xiToeplitzRecurrenceIdentity_atOrder_p_of_hell
    (m := m) (s := s) (p := p)
    (hk := hk)
    (hEll := xiToeplitzEllOutAt_p_fromRecurrenceC_of_row0
      (m := m) (s := s) (p := p)
      (hroute := hroute)
      (hwpop := hwpop))

end XiPacket
end Targets
end Hyperlocal
