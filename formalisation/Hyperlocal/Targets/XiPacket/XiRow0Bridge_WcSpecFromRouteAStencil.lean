import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcCoeff3RouteAStencil

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
Clean replacement for the historical `xiJetQuot_row0_wc_spec`.

This derives the row-0 Toeplitz equation for `wc`
from the Route-A analytic stencil.
-/
axiom xiJetQuot_row0_wc_fromStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (wc s) = 0

end XiPacket
end Targets
end Hyperlocal
