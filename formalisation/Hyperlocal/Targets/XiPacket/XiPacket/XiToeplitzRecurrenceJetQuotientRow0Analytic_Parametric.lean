import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SigmaFromRec2_Parametric
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators

variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]

/--
Parametric theorem-side sibling of the row-0 scalar-goals wrapper.

Policy:
* consume the clean parametric trio lane for `w0/wp2/wp3`
* leave `wc` on the existing theorem route for now
* do NOT install any instances here
* do NOT replace the public stable wrapper yet
-/
noncomputable def xiJetQuot_row0_scalarGoals_parametric
    (s : Hyperlocal.OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 := by
    exact row0Sigma_w0_eq_zero_fromRec2_parametric (s := s)
  hwc := by
    exact (_root_.Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_zero s)
  hwp2 := by
    exact row0Sigma_wp2_eq_zero_fromRec2_parametric (s := s)
  hwp3 := by
    exact row0Sigma_wp3_eq_zero_fromRec2_parametric (s := s)

end XiPacket
end Targets
end Hyperlocal
