/-
  Hyperlocal/OneButton.lean

  Purpose:
  Measure real axiom-reduction progress on the LIVE final-cone branches,
  rather than only printing the final wrapper theorem.

  Why this is better than `#print axioms offSeedPhaseLock_Xi` alone:
  the final phase-lock cone currently splits into two independent branches:

    Branch A: recurrence / bCoeff route
      xiBcoeff2_eq_zero, xiBcoeff3_eq_zero
      -> feeds the sine equalities
      -> currently carries:
           xiAtOrderCoords01Out_axiom_stub
           xiJetQuot_row0_w0At_spec
           xiJetQuot_row0_wc_spec
           xiJetQuot_row0_wp2At_spec
           xiJetQuot_row0_wp3At_spec

    Branch B: κ-side dslope route
      hkappaAt_of_dslopeIter_ne0
      -> currently carries:
           RouteAJetCoordAxioms.Wc.payload

  So progress should be measured at:
    * the final theorem,
    * the two immediate live consumers,
    * the exact row-0 root surfaces being attacked,
    * and the new clean theorem-parametric sibling surfaces.

  Policy:
  * no new mathematics
  * no new instances
  * only imports and `#print axioms`
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInject
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder_Theorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/-!
  Final theorem wrappers.
-/
#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi
#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi

/-!
  Branch A: recurrence / bCoeff route.
  These are the first live consumers that should shrink when row-0 / coords01
  work actually lands.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff2_eq_zero
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff3_eq_zero
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb2_fromRecurrence
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb3_fromRecurrence

/-!
  Branch B: κ-side dslope route.
  This is the separate final-cone branch carrying the remaining Route-A wc payload.
-/
#print axioms Hyperlocal.Targets.XiPacket.hkappaAt_of_dslopeIter_ne0
#print axioms Hyperlocal.Targets.XiPacket.xiJetNonflat_dslope_exists

/-!
  Exact row-0 roots.
  These are the surfaces whose disappearance is the concrete metric for
  actual upstream progress.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_w0At_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp2At_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp3At_spec_proof

/-!
  Public row-0 wrappers.
  Compare the old ambient wrapper against the new theorem-parametric sibling.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder_theorem
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder_theorem

/-!
  RecurrenceA bridge surfaces.
  Compare the old ambient shim against the new theorem-parametric sibling.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRec2AtOrder_fromRecurrenceA
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRec2AtOrder_fromRecurrenceA_theorem

/-!
  Shared coords01 producer root.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiAtOrderCoords01Out_axiom_stub

end Hyperlocal
