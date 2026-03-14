/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3WcRouteANormalForm.lean

  Normalize the remaining `wc` coefficient-3 goal to an explicit Route-A scalar identity.

  This file does NOT prove the final zero yet.
  It isolates the exact remaining proof obligation:
      (-2) * G''(1-ρ) + σ2 * G'(1-ρ) - σ3 * G(1-ρ) = 0
  for G = routeA_G s.

  POLICY:
  * use the lowered Route-A scalar seam
  * do NOT pull `RouteAJetCoordProvider` back in here
  * do NOT use `...WcCoordsFromRouteAJetLeibniz`
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Algebra
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderFromScalars
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

variable [RouteAWcScalarProvider]

/--
Raw Route-A normal form for the remaining `wc` coefficient-3 goal.
-/
theorem row0ConvCoeff3_wc_routeA_normalForm
    (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3
      =
        (-2 : ℂ) * (deriv (deriv (routeA_G s)) (1 - s.ρ))
        + (JetQuotOp.σ2 s) * (deriv (routeA_G s) (1 - s.ρ))
        - (JetQuotOp.σ3 s) * ((routeA_G s) (1 - s.ρ)) := by
  calc
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3
        =
          (-2 : ℂ) * (wc s (2 : Fin 3))
          + (JetQuotOp.σ2 s) * (wc s (1 : Fin 3))
          - (JetQuotOp.σ3 s) * (wc s (0 : Fin 3)) := by
            simpa using convCoeff3_eq_lincomb (s := s) (w := wc s)
    _   =
          (-2 : ℂ) * (deriv (deriv (routeA_G s)) (1 - s.ρ))
          + (JetQuotOp.σ2 s) * (deriv (routeA_G s) (1 - s.ρ))
          - (JetQuotOp.σ3 s) * ((routeA_G s) (1 - s.ρ)) := by
            rw [← JetQuotOp.routeA_G_wc_coord2 (s := s),
                ← JetQuotOp.routeA_G_wc_coord1 (s := s),
                ← JetQuotOp.routeA_G_wc_coord0 (s := s)]

/--
If the explicit Route-A scalar identity is supplied, the `wc` coefficient-3
goal follows immediately.

This is the exact theorem-side insertion point for the eventual real proof.
-/
theorem row0ConvCoeff3_wc_of_routeA_scalar
    (s : OffSeed Xi)
    (hroute :
      (-2 : ℂ) * (deriv (deriv (routeA_G s)) (1 - s.ρ))
        + (JetQuotOp.σ2 s) * (deriv (routeA_G s) (1 - s.ρ))
        - (JetQuotOp.σ3 s) * ((routeA_G s) (1 - s.ρ)) = 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  rw [row0ConvCoeff3_wc_routeA_normalForm (s := s)]
  exact hroute

end XiPacket
end Targets
end Hyperlocal
