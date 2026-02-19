/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart.lean

  Cycle-safe “analytic heart” interface for the AtOrder row--0 jet-quotient recurrence
  extraction.

  CHANGE (2026-02-19):
  The heart contract is derived from the cycle-safe Gate module (Row0ConvolutionAtRev axiom),
  not from the old Recurrence endpoint (which was importing the outer frontier and causing cycles).

  This file carries NO axiom: it packages the scalar heart contract (row0Sigma = 0) as the
  analytically natural output. The only remaining semantic insertion is the single axiom
  inside the Gate module.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGate
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
-/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0AtSigma  : row0Sigma s (w0At m s)  = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

/--
The AtOrder heart contract, derived from the cycle-safe Gate scalar goals.

Field-name agnostic: we destruct the scalar-goals structure by pattern matching,
so changes in the field names of `XiJetQuotRow0ScalarGoalsAtOrder` cannot break this file.
-/
theorem xiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0AtOrderHeartOut m s := by
  classical
  -- Gate gives the scalar goals bundle directly.
  -- IMPORTANT: do not access fields by name; destruct the constructor.
  rcases (xiJetQuotRow0ScalarGoalsAtOrder_fromGate (m := m) (s := s)) with ⟨h0, h2, h3⟩
  exact ⟨h0, h2, h3⟩

end XiPacket
end Targets
end Hyperlocal
