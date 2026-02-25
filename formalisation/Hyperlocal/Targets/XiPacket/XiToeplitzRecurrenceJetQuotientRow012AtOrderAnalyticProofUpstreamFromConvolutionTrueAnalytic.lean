/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalytic.lean

  Glue module for interface (B):

    [XiRow012UpstreamTrueAnalytic]
      ⇒ XiJetQuotRow012PropAtOrder (theorem-level)
      ⇒ XiJetQuotRow012AtOrder     (via Prop⇒Type bridge)

  This file introduces NO axioms.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRow012ConvolutionAtRevAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromPropBridge
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Upstream Prop-level Row012 payload derived from the true-analytic convolution bundle. -/
theorem xiJetQuotRow012PropAtOrder_trueAnalytic_upstream
    [XiRow012UpstreamTrueAnalytic] (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012PropAtOrder m s := by
  classical
  exact xiJetQuotRow012PropAtOrder_of_row012ConvolutionAtRevAtOrderOut
    (m := m) (s := s)
    (XiRow012UpstreamTrueAnalytic.row012_out (m := m) (s := s))

/-- Upstream Type-level Row012 target bundle (definitional packaging from Prop). -/
noncomputable def xiJetQuotRow012AtOrder_trueAnalytic_upstream
    [XiRow012UpstreamTrueAnalytic] (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_of_row012PropAtOrder (m := m) (s := s)
    (xiJetQuotRow012PropAtOrder_trueAnalytic_upstream (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
