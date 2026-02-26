/-
  Hyperlocal/Targets/XiPacket/XiRow012UpstreamTrueAnalyticFromRec2TrueAnalytic.lean

  Genuine analytic propagation (no refactor):

  Bridge the Prop-first upstream interface

      XiRow012UpstreamTrueAnalytic

  from the Rec2-gated true-analytic Row012 endpoint

      xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic

  This is useful for downstream rails that are written against the *upstream* gate,
  while the project is temporarily running on the Rec2-gated analytic spine.

  DAG / safety:
  * extractor-free
  * does not import any Row012 "analytic endpoint" axiom modules
  * only depends on the Rec2 true-analytic sigma install + the theorem-level
    Row012 reverse-convolution discharge.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Rec2-gated bridge:
`[XiJetQuotRec2AtOrderTrueAnalytic]` (via the sigma-free Row012 endpoint)
installs the Prop-first upstream bundle gate.
-/
instance (priority := 900)
    [XiJetQuotRec2AtOrderTrueAnalytic] : XiRow012UpstreamTrueAnalytic where
  row012_out := by
    intro m s
    simpa using (xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
