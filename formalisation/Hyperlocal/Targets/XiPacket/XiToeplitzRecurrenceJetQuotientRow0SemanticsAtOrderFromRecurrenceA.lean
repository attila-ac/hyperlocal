/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA.lean

  Route–A discharge landing pad for the (AtOrder) recurrence-natural semantic cliff.

  This file is cycle-safe (imports only defs + row012 target + Mathlib.Tactic).

  It provides:
    * toeplitzL_eq_zero_of_rows
    * xiJetQuotOpZeroAtOrder_of_row012   (local upgrader lemma)
    * xiJetQuotOpZeroAtOrder_fromRecurrenceA (derived from the row012 axiom)

  Remaining analytic cliff is isolated to:
    xiJetQuotRow012AtOrder_fromRecurrenceA
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
On `Fin 3`, rowwise equalities imply function equality.
-/
lemma toeplitzL_eq_zero_of_rows
    {s : OffSeed Xi} {w : Hyperlocal.Transport.Window 3}
    (h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0)
    (h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0)
    (h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0)
    : (toeplitzL 2 (JetQuotOp.aRk1 s) w) = 0 := by
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

/--
Upgrade rowwise equalities (rows 0/1/2) into the bundled full-window contract.
-/
theorem xiJetQuotOpZeroAtOrder_of_row012
    (m : ℕ) (s : OffSeed Xi)
    (h0 : XiJetQuotRow0WitnessCAtOrder m s)
    (h1_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (1 : Fin 3) = 0)
    (h2_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (2 : Fin 3) = 0)
    (h1_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (1 : Fin 3) = 0)
    (h2_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (2 : Fin 3) = 0)
    (h1_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (1 : Fin 3) = 0)
    (h2_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (2 : Fin 3) = 0)
    : XiJetQuotOpZeroAtOrder m s := by
  refine ⟨?_, ?_, ?_⟩
  ·
    exact toeplitzL_eq_zero_of_rows (s := s) (w := w0At m s)
      h0.hop_w0At h1_w0At h2_w0At
  ·
    exact toeplitzL_eq_zero_of_rows (s := s) (w := wp2At m s)
      h0.hop_wp2At h1_wp2At h2_wp2At
  ·
    exact toeplitzL_eq_zero_of_rows (s := s) (w := wp3At m s)
      h0.hop_wp3At h1_wp3At h2_wp3At

/-- Remaining analytic cliff: the recurrence extractor should output this row012 payload. -/
axiom xiJetQuotRow012AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s

/-- Route–A discharge point (derived from the row012 bundle). -/
theorem xiJetQuotOpZeroAtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  have H : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_fromRecurrenceA (m := m) (s := s)
  exact xiJetQuotOpZeroAtOrder_of_row012 (m := m) (s := s)
    (h0 := H.h0)
    (h1_w0At := H.h1_w0At)   (h2_w0At := H.h2_w0At)
    (h1_wp2At := H.h1_wp2At) (h2_wp2At := H.h2_wp2At)
    (h1_wp3At := H.h1_wp3At) (h2_wp3At := H.h2_wp3At)

end XiPacket
end Targets
end Hyperlocal
