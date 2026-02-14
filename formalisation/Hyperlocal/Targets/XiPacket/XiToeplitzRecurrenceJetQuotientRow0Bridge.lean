/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Bridge.lean

  Patch: make Route-B bridge axiom-free by repackaging
  `xiJetQuotRow0ConcreteExtract` (your concrete bundle).

  IMPORTANT:
  `XiJetQuotRow0RecurrenceExtract s` is a `Type`, not a `Prop`,
  so this must be a `def`, not a `theorem`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Semantics
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Hyperlocal.Transport

/-!
## Recurrence extraction (ξ-specific semantic input)

This file is now pure packaging: it is axiom-free.

All ξ-specific content is isolated in
`XiToeplitzRecurrenceJetQuotientRow0ConcreteExtract.lean`
(via its single remaining semantic placeholder).
-/

/--
Row-0 recurrence extraction bundle for the jet-quotient Toeplitz operator on the
four canonical ξ windows `w0/wc/wp2/wp3`.

(Kept in the downstream-facing shape expected by the Route-B pipeline.)
-/
structure XiJetQuotRow0RecurrenceExtract (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

/--
ξ-specific recurrence extraction at row 0 (now definition-level, axiom-free here):
repackage `xiJetQuotRow0ConcreteExtract`.
-/
def xiJetQuotRow0RecurrenceExtract (s : Hyperlocal.OffSeed Xi) :
  XiJetQuotRow0RecurrenceExtract s := by
  let h : XiJetQuotRow0ConcreteExtract s := xiJetQuotRow0ConcreteExtract (s := s)
  exact ⟨h.hop_w0, h.hop_wc, h.hop_wp2, h.hop_wp3⟩

/-!
## Bridge: recurrence extraction ⇒ row-0 witness
-/

/-- Bridge definition: recurrence extraction ⇒ row-0 witness. -/
def xiJetQuotRow0WitnessC (s : Hyperlocal.OffSeed Xi) : XiJetQuotRow0WitnessC s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (xiJetQuotRow0RecurrenceExtract s).hop_w0
  · exact (xiJetQuotRow0RecurrenceExtract s).hop_wc
  · exact (xiJetQuotRow0RecurrenceExtract s).hop_wp2
  · exact (xiJetQuotRow0RecurrenceExtract s).hop_wp3

end XiPacket
end Targets
end Hyperlocal
