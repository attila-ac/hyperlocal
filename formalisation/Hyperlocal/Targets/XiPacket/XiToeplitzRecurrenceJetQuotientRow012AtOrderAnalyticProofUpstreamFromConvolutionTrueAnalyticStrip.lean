/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalyticStrip.lean

  Strip-specialised glue module for the theorem-clean interface:

    [XiRow012UpstreamTrueAnalyticStrip]
      => XiJetQuotRow012PropAtOrder
      => XiJetQuotRow012AtOrder

  No axioms introduced here.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticStripInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRow012ConvolutionAtRevAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromPropBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiJetQuotRow012PropAtOrder_trueAnalytic_upstream_strip
    [XiRow012UpstreamTrueAnalyticStrip]
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiJetQuotRow012PropAtOrder m (s : OffSeed Xi) := by
  classical
  exact
    xiJetQuotRow012PropAtOrder_of_row012ConvolutionAtRevAtOrderOut
      (m := m) (s := (s : OffSeed Xi))
      (XiRow012UpstreamTrueAnalyticStrip.row012_out_strip (m := m) (s := s))

noncomputable def xiJetQuotRow012AtOrder_trueAnalytic_upstream_strip
    [XiRow012UpstreamTrueAnalyticStrip]
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiJetQuotRow012AtOrder m (s : OffSeed Xi) :=
  xiJetQuotRow012AtOrder_of_row012PropAtOrder
    (m := m) (s := (s : OffSeed Xi))
    (xiJetQuotRow012PropAtOrder_trueAnalytic_upstream_strip (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
