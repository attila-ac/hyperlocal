/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean

  Public row-0 concrete facts on the old acyclic seam.

  POLICY:
  * w0/wp2/wp3 come directly from the at-order proof lane
  * wc now uses the theorem-backed frontier theorem, not the thin seam axiom directly
  * do NOT import the stencil corridor here
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpecTheorem
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

variable [XiJetQuotRec2AtOrderTrueAnalytic]
variable [XiAtOrderSigmaProvider]
variable [XiAtOrderCoords01Provider]
variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [RouteAWcScalarProvider]

@[simp] lemma w0At_zero_row0Concrete (s : OffSeed Xi) : w0At 0 s = w0 s := by
  funext i
  simp [w0At, w0, xiTransportedJet, xiCentralJetAt, xiCentralJet, xiJet3At, cderivIter]

@[simp] lemma wp2At_zero_row0Concrete (s : OffSeed Xi) : wp2At 0 s = wp2 s := by
  funext i
  simp [wp2At, wpAt, wp2, w0At_zero_row0Concrete (s := s)]

@[simp] lemma wp3At_zero_row0Concrete (s : OffSeed Xi) : wp3At 0 s = wp3 s := by
  funext i
  simp [wp3At, wpAt, wp3, w0At_zero_row0Concrete (s := s)]

theorem xiJetQuot_row0_w0
    (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa [w0At_zero_row0Concrete (s := s)] using
    (xiJetQuot_row0_w0At_spec_proof (m := 0) (s := s))

theorem xiJetQuot_row0_wc
    (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  exact xiJetQuot_row0_wc_spec_theorem (s := s)

theorem xiJetQuot_row0_wp2
    (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa [wp2At_zero_row0Concrete (s := s)] using
    (xiJetQuot_row0_wp2At_spec_proof (m := 0) (s := s))

theorem xiJetQuot_row0_wp3
    (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa [wp3At_zero_row0Concrete (s := s)] using
    (xiJetQuot_row0_wp3At_spec_proof (m := 0) (s := s))

end XiPacket
end Targets
end Hyperlocal
