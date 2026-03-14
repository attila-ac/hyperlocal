/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrderIm.lean

  Public wrappers for imag-pivot AtOrder ell identities.

  2026-03-13 honest post-axiom state:
  * the upstream proof lane is now theorem-gated
  * therefore these wrappers can no longer remain assumption-free
  * they must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
      [RouteAWcScalarProvider]

  plus the explicit Route-A scalar-zero payload required by the `wc` branch.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderImProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem

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
Ell-out at order `m` for the imag-pivot columns:
`u0 = imVec3(w0At m s)`, `uc = reVec3(wc s)`, `up = imVec3(wp2At/wp3At m s)`.
-/
theorem xiToeplitzEllOutAtIm_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (imVec3 (wp3At m s)) = 0 :=
  xiToeplitzEllOutAtIm_fromRecurrenceC_proof (m := m) (s := s) (hroute := hroute)

/--
Ell-out at order `m` for the mixed imag-pivot configuration:
`u0 = imVec3(w0At m s)`, `uc = reVec3(wc s)`, `up = reVec3(wp2At/wp3At m s)`.
-/
theorem xiToeplitzEllOutAtImRe_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 ∧
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0 :=
  xiToeplitzEllOutAtImRe_fromRecurrenceC_proof (m := m) (s := s) (hroute := hroute)

/--
Auxiliary ell-out at order `m` for the mixed configuration with `up = reVec3(w0At m s)`.
-/
theorem xiToeplitzEllOutAtImRe_w0_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (w0At m s)) = 0 :=
  xiToeplitzEllOutAtImRe_w0_fromRecurrenceC_proof (m := m) (s := s) (hroute := hroute)

end XiPacket
end Targets
end Hyperlocal
