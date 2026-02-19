/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3SemanticAtOrder.lean

  Thin semantic layer: expose the AtOrder convCoeff=0 facts under stable theorem names,
  mirroring `XiRow0Bridge_Row0Coeff3Semantic.lean` (order-0).

  Fix: `convCoeff` is in `Hyperlocal.Cancellation`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3ExtractorAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Cancellation

theorem row0ConvCoeff3_eq_zero_w0At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_w0At (m := m) (s := s))

theorem row0ConvCoeff3_eq_zero_wp2At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wp2At (m := m) (s := s))

theorem row0ConvCoeff3_eq_zero_wp3At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wp3At (m := m) (s := s))

namespace Row0Coeff3SemanticAtOrderExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvCoeff3_eq_zero_w0At
   row0ConvCoeff3_eq_zero_wp2At
   row0ConvCoeff3_eq_zero_wp3At)
end Row0Coeff3SemanticAtOrderExport

end XiPacket
end Targets
end Hyperlocal
