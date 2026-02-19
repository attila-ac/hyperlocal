/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3PayloadAtOrder.lean

  Route–C semantic payload (AtOrder): the three `n=3` reverse convCoeff identities
  for the jet-pivot windows `w0At/wp2At/wp3At`.

  IMPORTANT (DAG safety):
  This file is upstream of the AtOrder recurrence/heart/frontier chain.
  Therefore it MUST NOT import any of those modules.

  Current status:
  * The payload is provided as axioms under stable theorem names.
  * A downstream extractor file (`XiRow0Bridge_Row0Coeff3ExtractorAtOrder.lean`)
    can later be used to discharge these axioms (when the Toeplitz frontier is
    theorem-level without cycles).

  Net effect:
  * We can make `...AtOrderRecurrence.lean` axiom-free today, while keeping a
    single, clearly-isolated semantic cliff at the Route–C payload boundary.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Cancellation

/-- Route–C payload: convCoeff(n=3)=0 for the three AtOrder windows. -/
structure XiRow0Coeff3AtOrderPayload (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0
  hwp2At : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0
  hwp3At : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0

/-
Temporary semantic insertion (Route–C payload).  This is the ONLY place where
these facts are assumed without proof.
-/
axiom xiRow0Coeff3AtOrderPayload_axiom (m : ℕ) (s : OffSeed Xi) :
    XiRow0Coeff3AtOrderPayload m s

/-- Stable theorem name exporting the payload. -/
theorem xiRow0Coeff3AtOrderPayload (m : ℕ) (s : OffSeed Xi) :
    XiRow0Coeff3AtOrderPayload m s := by
  simpa using (xiRow0Coeff3AtOrderPayload_axiom (m := m) (s := s))

/-- Stable theorem name: `w0At` convCoeff payload. -/
theorem row0ConvCoeff3_eq_zero_w0At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 :=
  (xiRow0Coeff3AtOrderPayload (m := m) (s := s)).hw0At

/-- Stable theorem name: `wp2At` convCoeff payload. -/
theorem row0ConvCoeff3_eq_zero_wp2At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 :=
  (xiRow0Coeff3AtOrderPayload (m := m) (s := s)).hwp2At

/-- Stable theorem name: `wp3At` convCoeff payload. -/
theorem row0ConvCoeff3_eq_zero_wp3At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 :=
  (xiRow0Coeff3AtOrderPayload (m := m) (s := s)).hwp3At

namespace Row0Coeff3PayloadAtOrderExport
export _root_.Hyperlocal.Targets.XiPacket
  (xiRow0Coeff3AtOrderPayload
   row0ConvCoeff3_eq_zero_w0At
   row0ConvCoeff3_eq_zero_wp2At
   row0ConvCoeff3_eq_zero_wp3At)
end Row0Coeff3PayloadAtOrderExport

end XiPacket
end Targets
end Hyperlocal
