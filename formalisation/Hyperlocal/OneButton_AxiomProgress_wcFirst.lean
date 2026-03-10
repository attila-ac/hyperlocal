/-
  Hyperlocal/OneButton_AxiomProgress_wcFirst.lean

  Purpose:
  Measure whether `xiJetQuot_row0_wc_spec` has actually disappeared from the
  LIVE recurrence / bCoeff branch and from the final phase-lock cone.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInject
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcrete
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Concrete
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOut_fromRecurrenceC
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb2_fromRecurrence
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb3_fromRecurrence
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff2_eq_zero
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff3_eq_zero
#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi
#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi

end Hyperlocal
