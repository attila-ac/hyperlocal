import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLImpossibility
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Route-A normalization at the canonical wc anchor.
Current proof route: use the existing Route-A wc coordinate surface together
with the definitional closed form of `wc`.
-/
theorem routeA_G_at_one_sub_rho
    (s : OffSeed Xi) :
    (routeA_G s) (1 - s.ρ) = 0 := by
  calc
    (routeA_G s) (1 - s.ρ) = wc s (0 : Fin 3) := by
      simpa using (wc_coord0_routeA (s := s)).symm
    _ = 0 := by
      simpa using (ToeplitzGuardrails.wc_apply_fin0 (s := s))

/--
First-derivative normalization at the canonical wc anchor.
-/
theorem routeA_G_deriv_at_one_sub_rho
    (s : OffSeed Xi) :
    deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ) := by
  calc
    deriv (routeA_G s) (1 - s.ρ) = wc s (1 : Fin 3) := by
      simpa using (wc_coord1_routeA (s := s)).symm
    _ = (1 : ℂ) := by
      simpa using (ToeplitzGuardrails.wc_apply_fin1 (s := s))

/--
Second-derivative normalization at the canonical wc anchor.
-/
theorem routeA_G_deriv2_at_one_sub_rho
    (s : OffSeed Xi) :
    deriv (deriv (routeA_G s)) (1 - s.ρ) = (XiTransport.delta s : ℂ) := by
  calc
    deriv (deriv (routeA_G s)) (1 - s.ρ) = wc s (2 : Fin 3) := by
      simpa using (wc_coord2_routeA (s := s)).symm
    _ = (XiTransport.delta s : ℂ) := by
      simpa using (ToeplitzGuardrails.wc_apply_fin2 (s := s))

end XiPacket
end Targets
end Hyperlocal
