/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012FromSequenceBridge.lean

  Step (algebraic reverse bridge, cycle-safe):

  Turn the padded-sequence order-2 recurrence

      JetQuotRec2 s (padSeq3 w)

  back into the finite-window Toeplitz row012 equalities on `Fin 3`.

  This is the direction needed to kill the remaining manuscript-facing axiom
  `xiJetQuotRow012PropAtOrder_fromRecurrenceA` once the true analytic recurrence
  on a concrete ℕ-indexed sequence has been proved.

  Design:
  * Purely algebraic (no analytic imports).
  * Consumes only: `padSeq3`, `JetQuotRec2`, Toeplitz row normal forms,
    and the Prop-level row012 statement.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientShiftedSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientManuscriptRow012PropAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
From recurrence to rowwise Toeplitz equalities (rows 0/1/2 on `Fin 3`).

Exported instantiation lemma:
`JetQuotRec2 s (padSeq3 w)` ⇒ `ToeplitzRow012Prop s w`.

Also provided:
`JetQuotRec2 s (shiftSeq3 m w)` ⇒ `ToeplitzRow012Prop s w`,
so the analytic extractor can target either padded or shifted sequence form.
-/

/-- Canonical instantiation: `JetQuotRec2 s (padSeq3 w)` implies the finite row012 Toeplitz equalities. -/
theorem toeplitzRow012Prop_of_jetQuotRec2_padSeq3
    (s : OffSeed Xi) (w : Window 3)
    (h : JetQuotRec2 s (padSeq3 w)) : ToeplitzRow012Prop s w := by
  classical
  -- abbreviate coefficients
  set a0 : ℂ := JetQuotOp.aRk1 s 0
  set a1 : ℂ := JetQuotOp.aRk1 s 1
  set a2 : ℂ := JetQuotOp.aRk1 s 2

  -- recurrence instances at n = 0,1,2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2

  -- row 0
  have h0' : (a0 * w 0 + a1 * w 1) + a2 * w 2 = 0 := by
    -- padSeq3 at 0,1,2 is exactly the window; no truncation term appears.
    simpa [JetQuotRec2, padSeq3, a0, a1, a2, add_assoc] using h0

  have row0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin0, a0, a1, a2] using h0'

  -- row 1
  have h1' : (a0 * w 1) + (a1 * w 2) = 0 := by
    -- At n=1 we see indices 1,2,3 and padSeq3 w 3 = 0.
    simpa [JetQuotRec2, padSeq3, a0, a1, a2,
      add_assoc, add_left_comm, add_comm] using h1

  have row1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin1, a0, a1, a2] using h1'

  -- row 2
  have h2' : (a0 * w 2) = 0 := by
    -- At n=2 we see indices 2,3,4 and padSeq3 w 3 = padSeq3 w 4 = 0.
    simpa [JetQuotRec2, padSeq3, a0, a1, a2,
      add_assoc, add_left_comm, add_comm] using h2

  have row2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin2, a0, a1, a2] using h2'

  exact ⟨row0, row1, row2⟩

/--
Shifted variant:
if the recurrence holds on the shifted embedding `shiftSeq3 m w`,
then the finite Toeplitz row012 equalities hold for the window `w`.

This is useful if the analytic extractor naturally proves a recurrence on a global
sequence whose restriction/embedding matches `shiftSeq3`.
-/
theorem toeplitzRow012Prop_of_jetQuotRec2_shiftSeq3
    (m : ℕ) (s : OffSeed Xi) (w : Window 3)
    (h : JetQuotRec2 s (shiftSeq3 m w)) : ToeplitzRow012Prop s w := by
  classical
  -- Reduce to the padded lemma by evaluating the shifted recurrence at `n = m + k`
  -- and rewriting `shiftSeq3 m w (m+k) = padSeq3 w k`.
  -- We package the needed instances k=0,1,2 into a `JetQuotRec2 s (padSeq3 w)` proof.
  have hPad : JetQuotRec2 s (padSeq3 w) := by
    intro k
    -- use recurrence at n = m + k
    have hk := h (m + k)
    -- rewrite the three shifted terms to padded terms using simp lemmas from ShiftedSequenceAtOrderDefs
    -- (shiftSeq3_of_eq_add).
    simpa [JetQuotRec2, shiftSeq3_of_eq_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
  exact toeplitzRow012Prop_of_jetQuotRec2_padSeq3 (s := s) (w := w) hPad

/--
Bridge (AtOrder): a bundled padded-sequence recurrence payload implies the manuscript-facing
finite-window row012 Prop payload.
-/
theorem xiJetQuotRow012PropAtOrder_of_rec2
    (m : ℕ) (s : OffSeed Xi)
    (H : XiJetQuotRec2AtOrder m s) : XiJetQuotRow012PropAtOrder m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact toeplitzRow012Prop_of_jetQuotRec2_padSeq3 (s := s) (w := w0At m s) (h := H.h_w0At)
  · exact toeplitzRow012Prop_of_jetQuotRec2_padSeq3 (s := s) (w := wp2At m s) (h := H.h_wp2At)
  · exact toeplitzRow012Prop_of_jetQuotRec2_padSeq3 (s := s) (w := wp3At m s) (h := H.h_wp3At)

end XiPacket
end Targets
end Hyperlocal
