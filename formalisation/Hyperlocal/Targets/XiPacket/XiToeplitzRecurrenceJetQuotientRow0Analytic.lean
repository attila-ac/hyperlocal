import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SigmaFromRec2_Parametric
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischarge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [XiAtOrderSigmaProvider]
variable [XiAtOrderCoords01Provider]

/--
Analytic row0 scalar goals using the **clean Rec2 trio route**.
`wc` remains on the legacy surface for now.
-/
noncomputable def xiJetQuot_row0_scalarGoals_analytic
    (s : OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s where
  hw0 :=
    row0Sigma_w0_eq_zero_fromRec2_parametric s
  hwc :=
    -- still legacy for now
    Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_zero s
  hwp2 :=
    row0Sigma_wp2_eq_zero_fromRec2_parametric s
  hwp3 :=
    row0Sigma_wp3_eq_zero_fromRec2_parametric s

/-- Public wrapper. -/
noncomputable def xiJetQuot_row0_scalarGoals
    (s : OffSeed Xi) :
    XiJetQuotRow0ScalarGoals s :=
  xiJetQuot_row0_scalarGoals_analytic s

end Hyperlocal.Targets.XiPacket
