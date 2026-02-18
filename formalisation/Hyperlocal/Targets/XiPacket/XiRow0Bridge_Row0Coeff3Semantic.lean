/-
REPLACE FILE CONTENT for:
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Semantic.lean

Fix:
  Stop referencing `_root_.Hyperlocal.Targets.XiPacket.row0ConvCoeff3_*`.
  After importing the extractor, the theorems are available in the *current*
  namespace, so use them directly.

  This avoids VSCode “unknown identifier” glitches caused by stale elaboration
  state / namespace qualification.
-/

/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Semantic.lean

  MOVE–3 semantic payload (theorem-level, upstream-extracted).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Extractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation

theorem row0ConvCoeff3_eq_zero_w0 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_w0 (s := s))

theorem row0ConvCoeff3_eq_zero_wc (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wc (s := s))

theorem row0ConvCoeff3_eq_zero_wp2 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wp2 (s := s))

theorem row0ConvCoeff3_eq_zero_wp3 (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wp3 (s := s))

namespace Row0Coeff3SemanticExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvCoeff3_eq_zero_w0
   row0ConvCoeff3_eq_zero_wc
   row0ConvCoeff3_eq_zero_wp2
   row0ConvCoeff3_eq_zero_wp3)
end Row0Coeff3SemanticExport

end XiPacket
end Targets
end Hyperlocal
