import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeFromWcStencil

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
The historical stencil-side `wc` row-0 sigma surface.

This is no longer an axiom. It is now a theorem alias to the
clean Route-A stencil discharge already proved upstream.
-/
theorem xiJetQuot_row0_wc_fromStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (wc s) = 0 := by
  simpa using row0Sigma_wc_eq_zero_fromWcStencil (s := s)

end XiPacket
end Targets
end Hyperlocal
