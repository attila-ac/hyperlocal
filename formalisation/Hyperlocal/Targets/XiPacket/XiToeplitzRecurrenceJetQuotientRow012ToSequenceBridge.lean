/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge.lean

  Step-0 rigor (combinatorics sanity / boundary regimes), converse direction:

  Show that the finite row-0/1/2 equalities for `toeplitzL 2` on `Window 3`
  are sufficient to obtain the order-2 recurrence on the padded infinite sequence `padSeq3`.

  For the padding convention `padSeq3`:
    • the recurrence at n = 0,1,2 is exactly rows 0,1,2 of `toeplitzL 2`,
    • for n ≥ 3 the recurrence becomes `0 = 0` by definitional padding.

  Cycle-safe and purely algebraic:
    imports only:
      * the row012 target bundle,
      * the Step-1 defs (padSeq3/JetQuotRec2),
      * the Prop-level row012 defs (defs-only),
      * existing Toeplitz row normal forms (fin0/fin1/fin2).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
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
From rowwise Toeplitz equalities (rows 0/1/2 on `Fin 3`) to the padded-sequence recurrence.
-/

/--
Core lemma: rows 0/1/2 of `toeplitzL 2` on a window `w : Window 3`
imply the order-2 recurrence on the padded sequence `padSeq3 w`.
-/
private lemma jetQuotRec2_of_rows
    (s : OffSeed Xi) (w : Window 3)
    (h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0)
    (h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0)
    (h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0)
    : JetQuotRec2 s (padSeq3 w) := by
  classical
  intro n
  cases n with
  | zero =>
      -- n = 0: row 0
      simpa [JetQuotRec2, padSeq3, toeplitzL_two_apply_fin0,
        add_assoc, add_left_comm, add_comm] using h0
  | succ n =>
      cases n with
      | zero =>
          -- n = 1: row 1, and the a2-term vanishes because padSeq3 w 3 = 0
          simpa [JetQuotRec2, padSeq3, toeplitzL_two_apply_fin1,
            add_assoc, add_left_comm, add_comm] using h1
      | succ n =>
          cases n with
          | zero =>
              -- n = 2: row 2, and the a1/a2-terms vanish because padSeq3 w 3 = padSeq3 w 4 = 0
              simpa [JetQuotRec2, padSeq3, toeplitzL_two_apply_fin2,
                add_assoc, add_left_comm, add_comm] using h2
          | succ n =>
              -- n ≥ 3: everything is padded to 0, so the recurrence is 0 = 0
              simp [JetQuotRec2, padSeq3_succ_succ_succ,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Convenience: Prop-level row012 Toeplitz payload implies the padded recurrence on `padSeq3`. -/
theorem jetQuotRec2_padSeq3_of_toeplitzRow012Prop
    (s : OffSeed Xi) (w : Window 3)
    (H : ToeplitzRow012Prop s w) :
    JetQuotRec2 s (padSeq3 w) :=
  jetQuotRec2_of_rows (s := s) (w := w) H.h0 H.h1 H.h2

/-!
Package-level corollaries: row012 payloads imply the *bundled* sequence recurrence payload (AtOrder).
-/

/--
From the **Type-valued** row012 payload `XiJetQuotRow012AtOrder`, recover the bundled padded-sequence
recurrence payload `XiJetQuotRec2AtOrder`.
-/
theorem xiJetQuotRec2AtOrder_of_row012
    (m : ℕ) (s : OffSeed Xi)
    (H : XiJetQuotRow012AtOrder m s) : XiJetQuotRec2AtOrder m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    exact jetQuotRec2_of_rows (s := s) (w := w0At m s)
      (h0 := H.h0.hop_w0At) (h1 := H.h1_w0At) (h2 := H.h2_w0At)
  ·
    exact jetQuotRec2_of_rows (s := s) (w := wp2At m s)
      (h0 := H.h0.hop_wp2At) (h1 := H.h1_wp2At) (h2 := H.h2_wp2At)
  ·
    exact jetQuotRec2_of_rows (s := s) (w := wp3At m s)
      (h0 := H.h0.hop_wp3At) (h1 := H.h1_wp3At) (h2 := H.h2_wp3At)

/--
From the **Prop-valued** row012 payload `XiJetQuotRow012PropAtOrder`, recover the bundled padded-sequence
recurrence payload `XiJetQuotRec2AtOrder`.
-/
theorem xiJetQuotRec2AtOrder_of_row012Prop
    (m : ℕ) (s : OffSeed Xi)
    (H : XiJetQuotRow012PropAtOrder m s) : XiJetQuotRec2AtOrder m s := by
  classical
  rcases H with ⟨Hw0, ⟨Hwp2, Hwp3⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := w0At m s) Hw0
  · exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp2At m s) Hwp2
  · exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp3At m s) Hwp3

end XiPacket
end Targets
end Hyperlocal
