/-
  Hyperlocal/Targets/XiPacket/XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream.lean

  Adapter (no refactor):
  Use the existing upstream Row012 reverse-convolution endpoint to instantiate the
  new Prop-class interface `XiRow012UpstreamTrueAnalytic`.

  This makes downstream code depend on the Prop-first class interface,
  while the real analytic proof can be swapped in later.

  No new axioms introduced by this adapter itself.
-/

import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Adapter: existing upstream endpoint ⇒ new Prop-first interface class. -/
instance (priority := 1000) : XiRow012UpstreamTrueAnalytic where
  row012_out := by
    intro m s
    simpa using (xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
