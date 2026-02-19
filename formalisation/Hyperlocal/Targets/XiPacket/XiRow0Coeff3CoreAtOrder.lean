/-
  Hyperlocal/Targets/XiPacket/XiRow0Coeff3CoreAtOrder.lean

  Upstream interface for AtOrder coeff-3 identities.
  Pure boundary layer (axioms only), DAG-safe.

  IMPORTANT:
  Do NOT import any frontier/concrete proof layers here, otherwise you
  create a build cycle because the frontier currently depends (indirectly)
  on this boundary via the Row0 convolution discharge.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Transport.OffSeedBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Cancellation

axiom row0ConvCoeff3_w0At
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (w0At m s)) 3 = 0

axiom row0ConvCoeff3_wp2At
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (wp2At m s)) 3 = 0

axiom row0ConvCoeff3_wp3At
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (wp3At m s)) 3 = 0

end XiPacket
end Targets
end Hyperlocal
