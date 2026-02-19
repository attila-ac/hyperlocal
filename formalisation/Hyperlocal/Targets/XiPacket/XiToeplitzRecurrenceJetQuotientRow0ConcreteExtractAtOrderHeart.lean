/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart.lean

  Cycle-safe “analytic heart” interface for the AtOrder row--0 jet-quotient recurrence
  extraction.

  CHANGE (2026-02-18):
  The heart contract is stated in the *scalar* form (`row0Sigma = 0`) rather than as
  Toeplitz row-0 equalities. This matches the natural output of a Cauchy/convolution proof.

  This file carries NO axiom: it derives the scalar heart contract from the (temporary)
  Type-level recurrence extraction endpoint isolated in
  `...AtOrderRecurrence.lean`.

  Once the true analytic recurrence theorem is proved, replace the axiom in
  `...AtOrderRecurrence.lean` by a theorem and leave this file unchanged.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderRecurrence
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Scalarize

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Scalar output shape of the concrete order-`m` jet-quotient recurrence extraction theorem.

This is the precise “analytic heart” contract we want to prove in the future.
-/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0AtSigma  : row0Sigma s (w0At m s)  = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

/--
The AtOrder heart contract, derived from the (temporary) recurrence extraction endpoint.

This is theorem-level already; the only remaining semantic insertion is the axiom
inside `...AtOrderRecurrence.lean`.
-/
theorem xiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0AtOrderHeartOut m s := by
  classical
  -- strongest (Type-level) recurrence extract
  let E := xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence (m := m) (s := s)
  refine ⟨?_, ?_, ?_⟩
  ·
    -- Toeplitz row-0 equality rewritten as row0Sigma
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)] using E.hop_w0At
  ·
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)] using E.hop_wp2At
  ·
    simpa [toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)] using E.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
