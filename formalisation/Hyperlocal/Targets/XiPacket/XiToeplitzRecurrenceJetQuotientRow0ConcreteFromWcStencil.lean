/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteFromWcStencil.lean

  Parallel theorem-side row-0 concrete producer.

  Purpose:
  * keep the historical ungated `XiToeplitzRecurrenceJetQuotientRow0Concrete.lean`
    untouched and build-green;
  * provide a parallel producer in which only the `wc` component is upgraded to
    the clean Route-A stencil proof;
  * expose the honest gate `[TAC.XiJetWindowEqAtOrderQuotProvider]` exactly here,
    and nowhere upstream of this file.

  Policy:
  * `w0/wp2/wp3` are reused from the existing theorem-side AtOrder route.
  * `wc` is discharged via `wc_convCoeff3_clean`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0SigmaToToeplitzRow0

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
  have hsigma : row0Sigma s (wc s) = 0 := by
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)] using
      (wc_convCoeff3_clean (s := s))
  exact toeplitz_row0_eq_zero_of_row0Sigma_eq_zero (s := s) (w := wc s) hsigma

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
