import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderRecurrence

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Output shape of the concrete order-`m` jet-quotient recurrence extraction theorem.

This is the precise “analytic heart” contract we want to prove in the future.
-/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0
  hwp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0
  hwp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

/--
SINGLE semantic endpoint (temporary): the concrete analytic extraction theorem
for order-`m` jets should produce `XiJetQuotRow0AtOrderHeartOut m s`.

This file should *not* postulate that theorem directly.
Instead, we derive it from the (future) concrete recurrence extraction theorem
isolated in `...AtOrderRecurrence.lean`.
-/
theorem xiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) :
  XiJetQuotRow0AtOrderHeartOut m s := by
  classical
  let E := xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrence (m := m) (s := s)
  refine ⟨?_, ?_, ?_⟩
  · exact E.hop_w0At
  · exact E.hop_wp2At
  · exact E.hop_wp3At

end XiPacket
end Targets
end Hyperlocal
