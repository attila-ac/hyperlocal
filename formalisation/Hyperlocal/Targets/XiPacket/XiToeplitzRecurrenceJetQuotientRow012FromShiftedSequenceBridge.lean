/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012FromShiftedSequenceBridge.lean

  Algebraic bridge (cycle-safe):

  If a shifted-support sequence satisfies the order-2 JetQuot recurrence,
  then the underlying Window-3 satisfies the finite Toeplitz row012 equalities.

  Key lemma:
      JetQuotRec2 s (shiftSeq3 m w) → ToeplitzRow012Prop s w

  This is the “instantiate at n=m,m+1,m+2 and rewrite” step that will be used
  once the true analytic recurrence is proved on a concrete sequence J_s and
  we identify J_s with a shifted window sequence.
-/

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
### Step 1: shiftSeq3 recurrence ⇒ padSeq3 recurrence
-/

/--
If the order-2 recurrence holds for the shifted-support sequence `shiftSeq3 m w`,
then it holds for the canonical padded sequence `padSeq3 w` (reindex by `n ↦ m+n`).
-/
lemma jetQuotRec2_padSeq3_of_shiftSeq3
    (m : ℕ) (s : OffSeed Xi) (w : Window 3)
    (h : JetQuotRec2 s (shiftSeq3 m w)) :
    JetQuotRec2 s (padSeq3 w) := by
  intro n
  -- apply the shifted recurrence at index m+n
  have hn := h (m + n)
  -- rewrite the three terms using `shiftSeq3_of_eq_add`
  -- (m+n)+1 = m+(n+1), (m+n)+2 = m+(n+2)
  simpa [JetQuotRec2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn

/-!
### Step 2: padSeq3 recurrence ⇒ Toeplitz row012 equalities
-/

/--
Padded-sequence recurrence implies the finite-window Toeplitz row012 contract.

(This is the non-AtOrder, single-window form.)
-/
lemma toeplitzRow012Prop_of_jetQuotRec2_padSeq3
    (s : OffSeed Xi) (w : Window 3)
    (h : JetQuotRec2 s (padSeq3 w)) :
    ToeplitzRow012Prop s w := by
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
    simpa [JetQuotRec2, padSeq3, a0, a1, a2, add_assoc] using h0
  have row0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin0, a0, a1, a2] using h0'

  -- row 1
  have h1' : (a0 * w 1) + (a1 * w 2) = 0 := by
    -- padSeq3 w 3 = 0 kills the a2-term
    simpa [JetQuotRec2, padSeq3, a0, a1, a2, add_assoc, add_left_comm, add_comm] using h1
  have row1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin1, a0, a1, a2] using h1'

  -- row 2
  have h2' : (a0 * w 2) = 0 := by
    -- padSeq3 w 3 = padSeq3 w 4 = 0 kill the a1/a2-terms
    simpa [JetQuotRec2, padSeq3, a0, a1, a2, add_assoc, add_left_comm, add_comm] using h2
  have row2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 := by
    simpa [toeplitzL_two_apply_fin2, a0, a1, a2] using h2'

  exact ⟨row0, row1, row2⟩

/-!
### Combined one-liner: shiftSeq3 recurrence ⇒ Toeplitz row012 on the window
-/

/--
**Single lemma (the “push harder” bridge):**

If the recurrence holds on the shifted-support sequence `shiftSeq3 m w`,
then the finite Toeplitz row012 equalities hold on the underlying window `w`.
-/
theorem toeplitzRow012Prop_of_jetQuotRec2_shiftSeq3
    (m : ℕ) (s : OffSeed Xi) (w : Window 3)
    (h : JetQuotRec2 s (shiftSeq3 m w)) :
    ToeplitzRow012Prop s w := by
  -- reindex to padSeq3 and discharge via the existing row012 algebra
  exact toeplitzRow012Prop_of_jetQuotRec2_padSeq3 (s := s) (w := w)
    (jetQuotRec2_padSeq3_of_shiftSeq3 (m := m) (s := s) (w := w) h)

end XiPacket
end Targets
end Hyperlocal
