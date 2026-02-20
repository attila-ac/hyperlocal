/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA.lean

  Landing pad (CLI-proof):

  DO NOT reference any “row012 builder” name (it was renamed / not exported in your
  current untracked bridge file, hence the Unknown identifier error).

  Instead, derive everything directly from the *theorem-level* recurrence payload

    xiJetQuotRec2AtOrder_fromRecurrenceA : XiJetQuotRec2AtOrder m s

  and convert that recurrence into the needed row-0/1/2 Toeplitz equalities using
  the already-available row normal forms (fin0/fin1/fin2).

  This keeps the analytic cliff isolated where you want it:
    the only remaining axiom in the Route–A boundary is
      `xiJetQuotRec2AtOrder_fromRecurrenceA`.

  The manuscript-facing Prop payload is now theorem-level and downstream:
    `xiJetQuotRow012PropAtOrder_fromRecurrenceA` is derived from the recurrence
    payload by the bridge `xiJetQuotRow012PropAtOrder_of_rec2`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

-- Recurrence payload (Route–A boundary; currently axiomatic)
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA

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

/-
Bridge lemmas: JetQuotRec2 on the padded Window-3 sequence implies Toeplitz rows 0/1/2 = 0.
These are the same computations you had in the “SequenceToRow012Bridge”, but localised here
so we do not depend on any particular exported def name.
-/

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

/-- Route–A discharge point: theorem-level, derived from the recurrence payload. -/
theorem xiJetQuotOpZeroAtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  -- recurrence payload (Route–A boundary)
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA (m := m) (s := s)

  -- row-0 witness package
  have h0_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2 (s := s) (w := w0At m s) Hrec.h_w0At
  have h0_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2 (s := s) (w := wp2At m s) Hrec.h_wp2At
  have h0_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2 (s := s) (w := wp3At m s) Hrec.h_wp3At

  have h0 : XiJetQuotRow0WitnessCAtOrder m s := ⟨h0_w0At, h0_wp2At, h0_wp3At⟩

  -- remaining rows from the same recurrence payload
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
