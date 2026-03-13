import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
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
This is the true missing upstream scalar source for the wc provider kill.
-/
theorem routeA_G_at_one_sub_rho
    (s : OffSeed Xi) :
    (routeA_G s) (1 - s.ρ) = 0 := by
  sorry

/--
First-derivative normalization at the canonical wc anchor.
-/
theorem routeA_G_deriv_at_one_sub_rho
    (s : OffSeed Xi) :
    deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ) := by
  sorry

/--
Second-derivative normalization at the canonical wc anchor.
-/
theorem routeA_G_deriv2_at_one_sub_rho
    (s : OffSeed Xi) :
    deriv (deriv (routeA_G s)) (1 - s.ρ) = (XiTransport.delta s : ℂ) := by
  sorry

end XiPacket
end Targets
end Hyperlocal
