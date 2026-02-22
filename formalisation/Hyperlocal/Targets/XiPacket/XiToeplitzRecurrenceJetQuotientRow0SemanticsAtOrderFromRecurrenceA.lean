/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA.lean

  Landing pad (cycle-safe, provider-based):

  This file no longer imports the Route–A recurrence axiom module directly.
  Instead it consumes the recurrence payload via the typeclass provider:

    [XiJetQuotRec2AtOrderProvider]  ⟹  XiJetQuotRec2AtOrder m s

  This concentrates the remaining semantic cliff into a small provider instance file.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

-- Recurrence payload interface (provider)
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider

-- Toeplitz row normal forms: toeplitzL_two_apply_fin0/fin1/fin2
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-- On `Fin 3`, rowwise equalities imply function equality. -/
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

/-- Upgrade row012 equalities into the full-window contract. -/
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

private lemma row0_eq_zero_of_rec2
    (s : OffSeed Xi) (w : Window 3)
    (hrec : JetQuotRec2 s (padSeq3 w)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
  have h0' :
      (JetQuotOp.aRk1 s 0) * w 0
        + (JetQuotOp.aRk1 s 1) * w 1
        + (JetQuotOp.aRk1 s 2) * w 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 0)
  simpa [toeplitzL_two_apply_fin0, add_assoc, add_left_comm, add_comm] using h0'

private lemma row1_eq_zero_of_rec2
    (s : OffSeed Xi) (w : Window 3)
    (hrec : JetQuotRec2 s (padSeq3 w)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 := by
  have h1' :
      (JetQuotOp.aRk1 s 0) * w 1
        + (JetQuotOp.aRk1 s 1) * w 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 1)
  simpa [toeplitzL_two_apply_fin1, add_assoc, add_left_comm, add_comm] using h1'

private lemma row2_eq_zero_of_rec2
    (s : OffSeed Xi) (w : Window 3)
    (hrec : JetQuotRec2 s (padSeq3 w)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 := by
  have h2' : (JetQuotOp.aRk1 s 0) * w 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 2)
  simpa [toeplitzL_two_apply_fin2] using h2'

/--
Route–A discharge point: theorem-level, derived from the *provided* recurrence payload.

No axiom imports here; the only remaining cliff is the provider instance.
-/
theorem xiJetQuotOpZeroAtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    XiJetQuotOpZeroAtOrder m s := by
  classical
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_provided (m := m) (s := s)

  have h0_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2 (s := s) (w := w0At m s) Hrec.h_w0At
  have h0_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2 (s := s) (w := wp2At m s) Hrec.h_wp2At
  have h0_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2 (s := s) (w := wp3At m s) Hrec.h_wp3At

  have h0 : XiJetQuotRow0WitnessCAtOrder m s := ⟨h0_w0At, h0_wp2At, h0_wp3At⟩

  have h1_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (1 : Fin 3) = 0 :=
    row1_eq_zero_of_rec2 (s := s) (w := w0At m s)  Hrec.h_w0At
  have h2_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (2 : Fin 3) = 0 :=
    row2_eq_zero_of_rec2 (s := s) (w := w0At m s)  Hrec.h_w0At

  have h1_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (1 : Fin 3) = 0 :=
    row1_eq_zero_of_rec2 (s := s) (w := wp2At m s) Hrec.h_wp2At
  have h2_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (2 : Fin 3) = 0 :=
    row2_eq_zero_of_rec2 (s := s) (w := wp2At m s) Hrec.h_wp2At

  have h1_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (1 : Fin 3) = 0 :=
    row1_eq_zero_of_rec2 (s := s) (w := wp3At m s) Hrec.h_wp3At
  have h2_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (2 : Fin 3) = 0 :=
    row2_eq_zero_of_rec2 (s := s) (w := wp3At m s) Hrec.h_wp3At

  exact xiJetQuotOpZeroAtOrder_of_row012 (m := m) (s := s)
    (h0 := h0)
    (h1_w0At := h1_w0At)   (h2_w0At := h2_w0At)
    (h1_wp2At := h1_wp2At) (h2_wp2At := h2_wp2At)
    (h1_wp3At := h1_wp3At) (h2_wp3At := h2_wp3At)

end XiPacket
end Targets
end Hyperlocal
