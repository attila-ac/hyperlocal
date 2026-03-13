/-
  Hyperlocal/OneButton.lean

  Purpose:
  Measure real axiom-reduction progress on the LIVE final-cone branches,
  and also include the RH-facing ζ <- ξ transfer checkpoint.

  Why this is better than `#print axioms offSeedPhaseLock_Xi` alone:
  the final phase-lock cone now has a much cleaner live burden picture:

    Branch A: recurrence / bCoeff / phase-lock route
      xiBcoeff2_eq_zero, xiBcoeff3_eq_zero
      -> feeds the sine equalities
      -> now visibly carries mainly:
           offSeed_in_critical_strip_of_trueanalytic
           routeA_stencil_zero
         with some more local recurrenceA / wc seams still carrying:
           xiAtOrderSigmaOut_axiom

    Branch B: κ-side dslope route
      hkappaAt_of_dslopeIter_ne0
      -> currently appears theorem-clean at the project-axiom level.

  So progress should be measured at:
    * the final XiPacket theorem wrappers,
    * the immediate live branch consumers,
    * the exact row-0 roots still worth watching,
    * the theorem-parametric sibling surfaces,
    * and the RH-facing ζ <- ξ transfer checkpoint.

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
import Hyperlocal.Targets.ZetaTransfer

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/-!
  Final XiPacket theorem wrappers.
-/
#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi
#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi

/-!
  Branch A: recurrence / bCoeff route.
  These are still the first live consumers that should shrink when the remaining
  strip / stencil burden is reduced.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff2_eq_zero
#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff3_eq_zero
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb2_fromRecurrence
#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb3_fromRecurrence

/-!
  Branch B: κ-side dslope route.
  This is the separate final-cone branch; currently useful as a cleanliness check.
-/
#print axioms Hyperlocal.Targets.XiPacket.hkappaAt_of_dslopeIter_ne0
#print axioms Hyperlocal.Targets.XiPacket.xiJetNonflat_dslope_exists

/-!
  Exact row-0 roots still worth watching.
  These remain the best local probes for residual strip / stencil / sigma burden.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_w0At_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp2At_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp3At_spec_proof

/-!
  Public row-0 wrappers.
  Compare the ambient wrapper against the theorem-parametric sibling.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder_theorem
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder_theorem

/-!
  RecurrenceA bridge surfaces.
  Compare the ambient shim against the theorem-parametric sibling.
-/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRec2AtOrder_fromRecurrenceA
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRec2AtOrder_fromRecurrenceA_theorem

/-!
  RH-facing ζ <- ξ transfer checkpoints.
  These are closer to the actual endgame theorem than the local XiPacket cone.
-/
#print axioms Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
#print axioms Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta

end Hyperlocal
