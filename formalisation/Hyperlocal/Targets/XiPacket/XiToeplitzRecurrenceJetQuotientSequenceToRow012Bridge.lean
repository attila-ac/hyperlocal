/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge.lean

  Step-0 rigor (combinatorics sanity / boundary regimes), converse direction:

  Show that the finite row-0/1/2 equalities for `toeplitzL 2` on `Window 3`
  are equivalent to the order-2 recurrence on the padded infinite sequence `padSeq3`.

  In particular, for the padding convention `padSeq3`:
    • the recurrence at n = 0,1,2 is exactly rows 0,1,2 of `toeplitzL 2`,
    • for n ≥ 3 the recurrence becomes `0 = 0` by definitional padding.

  This file is cycle-safe and purely algebraic:
    imports only the row012 target bundle, the Step-1 defs (padSeq3/JetQuotRec2),
    and the existing Toeplitz row normal forms (fin0/fin1/fin2).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
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

private lemma jetQuotRec2_of_rows
    (s : OffSeed Xi) (w : Window 3)
    (h0 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0)
    (h1 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0)
    (h2 : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0)
    : JetQuotRec2 s (padSeq3 w) := by
  intro n
  cases n with
  | zero =>
      -- row 0
      -- normal form: (toeplitzL ...) 0 = (a0*w0 + a1*w1) + a2*w2
      have : (JetQuotOp.aRk1 s 0) * w 0
            + (JetQuotOp.aRk1 s 1) * w 1
            + (JetQuotOp.aRk1 s 2) * w 2 = 0 := by
        -- rewrite h0 into the linear combination form
        -- (a0*w0 + a1*w1) + a2*w2 = 0  ⇒  a0*w0 + a1*w1 + a2*w2 = 0
        -- (simp with the known row-0 normal form)
        simpa [toeplitzL_two_apply_fin0, add_assoc, add_left_comm, add_comm] using h0
      -- now rewrite the recurrence at n=0 using padSeq3
      simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using this
  | succ n =>
      cases n with
      | zero =>
          -- n = 1 : row 1 (a2 term vanishes by padding)
          have : (JetQuotOp.aRk1 s 0) * w 1
                + (JetQuotOp.aRk1 s 1) * w 2 = 0 := by
            simpa [toeplitzL_two_apply_fin1, add_assoc, add_left_comm, add_comm] using h1
          -- recurrence at n=1: a0*w1 + a1*w2 + a2*0 = 0
          simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using this
      | succ n =>
          cases n with
          | zero =>
              -- n = 2 : row 2 (a1,a2 terms vanish by padding)
              have : (JetQuotOp.aRk1 s 0) * w 2 = 0 := by
                simpa [toeplitzL_two_apply_fin2] using h2
              simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using this
          | succ n =>
              -- n ≥ 3 : everything is padded to 0
              -- write n = k+3 in succ-succ-succ form
              -- (the simp lemma `padSeq3_succ_succ_succ` reduces all terms to 0)
              simp [JetQuotRec2, padSeq3_succ_succ_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-!
Package-level corollary: row012 payload implies the sequence recurrence payload.
This is the “converse” of `SequenceToRow012Bridge` and closes Step-0 formally.
-/

/-- From a row012 payload, recover the bundled padded-sequence recurrence payload. -/
theorem xiJetQuotRec2AtOrder_of_row012
    (m : ℕ) (s : OffSeed Xi)
    (H : XiJetQuotRow012AtOrder m s) : XiJetQuotRec2AtOrder m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    -- w0At
    exact jetQuotRec2_of_rows (s := s) (w := w0At m s)
      (h0 := H.h0.hop_w0At) (h1 := H.h1_w0At) (h2 := H.h2_w0At)
  ·
    -- wp2At
    exact jetQuotRec2_of_rows (s := s) (w := wp2At m s)
      (h0 := H.h0.hop_wp2At) (h1 := H.h1_wp2At) (h2 := H.h2_wp2At)
  ·
    -- wp3At
    exact jetQuotRec2_of_rows (s := s) (w := wp3At m s)
      (h0 := H.h0.hop_wp3At) (h1 := H.h1_wp3At) (h2 := H.h2_wp3At)


end XiPacket
end Targets
end Hyperlocal
