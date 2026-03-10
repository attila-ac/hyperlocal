/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil.lean

  Parallel theorem-side row-0 concrete producer.

  Purpose:
  * keep the historical ungated `XiToeplitzRecurrenceJetQuotientRow0Concrete.lean`
    untouched and build-green;
  * provide a parallel producer in which only the `wc` component is upgraded to
    the Route-A stencil discharge lane;
  * expose the honest gate `[TAC.XiJetWindowEqAtOrderQuotProvider]` exactly here.

  Policy:
  * `w0/wp2/wp3` are reused from the existing theorem-side AtOrder route.
  * `wc` is discharged directly via the packaged row-0 sigma theorem.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeFromWcStencil
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0SigmaToToeplitzRow0
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

lemma w0At_zero_fromWcStencil (s : OffSeed Xi) : w0At 0 s = w0 s := by
  funext i
  simp [w0At, w0, xiTransportedJet, xiCentralJetAt, xiCentralJet, xiJet3At, cderivIter]

lemma wp2At_zero_fromWcStencil (s : OffSeed Xi) : wp2At 0 s = wp2 s := by
  funext i
  simp [wp2At, wpAt, wp2, w0At_zero_fromWcStencil (s := s)]

lemma wp3At_zero_fromWcStencil (s : OffSeed Xi) : wp3At 0 s = wp3 s := by
  funext i
  simp [wp3At, wpAt, wp3, w0At_zero_fromWcStencil (s := s)]

theorem xiJetQuot_row0_w0_fromWcStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa [w0At_zero_fromWcStencil (s := s)] using
    (xiJetQuot_row0_w0At_spec_proof (m := 0) (s := s))

theorem xiJetQuot_row0_wc_fromWcStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  have hsigma : row0Sigma s (wc s) = 0 :=
    row0Sigma_wc_eq_zero_fromWcStencil (s := s)
  exact
    toeplitz_row0_eq_zero_of_row0Sigma_eq_zero (s := s) (w := wc s) hsigma

theorem xiJetQuot_row0_wp2_fromWcStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa [wp2At_zero_fromWcStencil (s := s)] using
    (xiJetQuot_row0_wp2At_spec_proof (m := 0) (s := s))

theorem xiJetQuot_row0_wp3_fromWcStencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa [wp3At_zero_fromWcStencil (s := s)] using
    (xiJetQuot_row0_wp3At_spec_proof (m := 0) (s := s))

end XiPacket
end Targets
end Hyperlocal
