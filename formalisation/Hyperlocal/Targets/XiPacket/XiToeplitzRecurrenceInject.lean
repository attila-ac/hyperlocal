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
open Hyperlocal.Transport.PrimeTrigPacket

/-- Consumer lemma: `bCoeff(2)=0` from the Toeplitz recurrence, via the pivot gate. -/
theorem xiToeplitz_hb2_fromRecurrence
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * routeA_G s (1 - s.ρ) = 0) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  simpa using
    (xiToeplitzRecurrenceIdentity_p
      (s := s) (hroute := hroute) (p := (2 : ℝ)) (hp := Or.inl rfl))

/-- Consumer lemma: `bCoeff(3)=0` from the Toeplitz recurrence, via the pivot gate. -/
theorem xiToeplitz_hb3_fromRecurrence
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * routeA_G s (1 - s.ρ) = 0) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  simpa using
    (xiToeplitzRecurrenceIdentity_p
      (s := s) (hroute := hroute) (p := (3 : ℝ)) (hp := Or.inr rfl))

end XiPacket
end Targets
end Hyperlocal
