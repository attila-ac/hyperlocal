/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentityRe.lean

  Real-pivot half only:
    * order-m lemma consuming `kappaAt m s ≠ 0`
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
  ·
    have hmul :
        bCoeff (σ s) (t s) (2 : ℝ) *
            kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      have h := hell.hell2
      rw [ell_wp2At_eq_b_mul_kappa (m := m) (s := s)] at h
      simpa using h

    have hmul' : bCoeff (σ s) (t s) (2 : ℝ) * kappaAt m s = 0 := by
      simpa [kappaAt, mul_assoc] using hmul

    exact (mul_eq_zero.mp hmul').resolve_right hk
  ·
    have hmul :
        bCoeff (σ s) (t s) (3 : ℝ) *
            kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      have h := hell.hell3
      rw [ell_wp3At_eq_b_mul_kappa (m := m) (s := s)] at h
      simpa using h

    have hmul' : bCoeff (σ s) (t s) (3 : ℝ) * kappaAt m s = 0 := by
      simpa [kappaAt, mul_assoc] using hmul

    exact (mul_eq_zero.mp hmul').resolve_right hk

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

end XiPacket
end Targets
end Hyperlocal
