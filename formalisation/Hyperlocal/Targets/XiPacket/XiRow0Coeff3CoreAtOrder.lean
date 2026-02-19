/-
  Hyperlocal/Targets/XiPacket/XiRow0Coeff3CoreAtOrder.lean

  Upstream interface for AtOrder coeff-3 identities.

  CHANGE (2026-02-19): retire the coeff-3 axioms.
  These identities are now discharged from the cycle-safe AtOrder Gate.
  This file remains the stable import point for `row0ConvCoeff3_*`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Coeff3CoreAtOrderProof

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Cancellation

theorem row0ConvCoeff3_w0At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
  simpa using row0ConvCoeff3_w0At_proof (m := m) (s := s)

theorem row0ConvCoeff3_wp2At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
  simpa using row0ConvCoeff3_wp2At_proof (m := m) (s := s)

theorem row0ConvCoeff3_wp3At (m : ℕ) (s : OffSeed Xi) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
  simpa using row0ConvCoeff3_wp3At_proof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
