/-
  Hyperlocal/Targets/XiPacket/XiRow0Coeff3CoreAtOrder.lean

  CORE interface for AtOrder coeff-3 identities.

  This file is the upstream semantic boundary for the AtOrder
  Row-0 coefficient extraction.

  IMPORTANT:
  • This file must remain upstream-safe.
  • It must NOT import Frontier / Recurrence / Heart.
  • It declares exactly three axioms.
  • Downstream convergence will later replace these with real proofs.

  Do NOT delete this file unless the entire upstream chain
  has been refactored to no longer depend on it.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiTransportConvolution

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Cancellation

/--
coeff-3 identity for `w0At`.

Interface boundary only.
-/
axiom row0ConvCoeff3_w0At
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (w0At m s)) 3 = 0

/--
coeff-3 identity for `wp2At`.

Interface boundary only.
-/
axiom row0ConvCoeff3_wp2At
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (wp2At m s)) 3 = 0

/--
coeff-3 identity for `wp3At`.

Interface boundary only.
-/
axiom row0ConvCoeff3_wp3At
    (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s)
              (winSeqRev (wp3At m s)) 3 = 0

end XiPacket
end Targets
end Hyperlocal
