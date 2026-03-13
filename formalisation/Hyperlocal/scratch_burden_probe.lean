/-
  Hyperlocal/scratch_burden_probe.lean

  Purpose:
  Fast probe for the real remaining burden after each refactor round.

  Policy:
  * no new mathematics
  * no instances
  * only imports and #print axioms
-/

import Hyperlocal.OneButton
import Hyperlocal.Cancellation.ImagAxisResultant
import Hyperlocal.Targets.ZetaTransfer
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Axioms
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcAxioms
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_WcJetProviderFromScalars
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/- Final XiPacket phase-lock checkpoints. -/
#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi
#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi

/- RH-facing ζ <- ξ transfer checkpoints. -/
#print axioms Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi
#print axioms Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta

/- Main live wrapper seam. -/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRec2AtOrder_fromRecurrenceA

/- Clean theorem-parametric siblings for comparison. -/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder_theorem
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder_theorem
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRec2AtOrder_fromRecurrenceA_theorem

/- Exact row-0 roots still worth watching. -/
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_w0At_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wc_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp2At_spec_proof
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp3At_spec_proof

/- Remaining declared project axioms. -/
#print axioms Hyperlocal.Targets.XiPacket.offSeed_in_critical_strip_of_trueanalytic
#print axioms Hyperlocal.Targets.XiPacket.xiAtOrderSigmaOut_axiom
#print axioms Hyperlocal.Targets.XiPacket.routeAJetCoordProvider_axiom
#print axioms Hyperlocal.Targets.XiPacket.routeA_stencil_zero

/- Residual wc scalar proof-hole seam. -/
#print axioms Hyperlocal.Targets.XiPacket.JetQuotOp.routeA_G_wc_coord0
#print axioms Hyperlocal.Targets.XiPacket.JetQuotOp.routeA_G_wc_coord1
#print axioms Hyperlocal.Targets.XiPacket.JetQuotOp.routeA_G_wc_coord2
#print axioms Hyperlocal.Targets.XiPacket.JetQuotOp.wc_isJet3At_routeA

end Hyperlocal
