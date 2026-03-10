/-
  Hyperlocal/OneButton_AxiomProgress_wcSecondWave.lean

  Purpose:
  Determine whether the remaining `wc` dirt is:
    (A) only on the exported ell-out wrapper surfaces, or
    (B) still inside the updated upstream proof theorems themselves.

  This is the decisive measurement after the first partial `wc` splice.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInject
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcrete
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderIm
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderImProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/- Root old/new wc surfaces. -/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc_fromWcStencil
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc_spec_proof

/- Upstream proof theorems: these should tell us whether the proof lane is actually clean. -/
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAt_fromRecurrenceC_proof
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtIm_fromRecurrenceC_proof
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_fromRecurrenceC_proof
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_w0_fromRecurrenceC_proof

/- Exported AtOrder wrappers. -/
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAt_fromRecurrenceC
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtIm_fromRecurrenceC
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_fromRecurrenceC
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_w0_fromRecurrenceC

/- Exported non-AtOrder wrapper. -/
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOut_fromRecurrenceC

/- Downstream consumers. -/
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb2_fromRecurrence
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb3_fromRecurrence
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff2_eq_zero
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff3_eq_zero
#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi
#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi

end Hyperlocal
