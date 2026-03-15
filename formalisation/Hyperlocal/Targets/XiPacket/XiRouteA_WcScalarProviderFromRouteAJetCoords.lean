-- formalisation/Hyperlocal/Targets/XiPacket/XiRouteA_WcScalarProviderFromRouteAJetCoords.lean

import Hyperlocal.Targets.XiPacket.XiRouteA_WcNormalization
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLImpossibility
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace ToeplitzGuardrails
open Hyperlocal.Targets.XiPacket.ToeplitzGuardrails
end ToeplitzGuardrails

instance (priority := 1000)
    [RouteAJetCoordProvider] : RouteAWcScalarProvider where
  routeA_G_at_one_sub_rho := by
    intro s
    calc
      (routeA_G s) (1 - s.ρ)
          = wc s (0 : Fin 3) := by
              simpa using (RouteAJetCoordProvider.wc_0 (s := s)).symm
      _ = 0 := by
              simpa using (ToeplitzGuardrails.wc_apply_fin0 (s := s))

  routeA_G_deriv_at_one_sub_rho := by
    intro s
    calc
      deriv (routeA_G s) (1 - s.ρ)
          = wc s (1 : Fin 3) := by
              simpa using (RouteAJetCoordProvider.wc_1 (s := s)).symm
      _ = (1 : ℂ) := by
              simpa using (ToeplitzGuardrails.wc_apply_fin1 (s := s))

  routeA_G_deriv2_at_one_sub_rho := by
    intro s
    calc
      deriv (deriv (routeA_G s)) (1 - s.ρ)
          = wc s (2 : Fin 3) := by
              simpa using (RouteAJetCoordProvider.wc_2 (s := s)).symm
      _ = (XiTransport.delta s : ℂ) := by
              simpa using (ToeplitzGuardrails.wc_apply_fin2 (s := s))

end XiPacket
end Targets
end Hyperlocal
