/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs.lean

  Step 1 (cycle-safe, defs-only):
  Minimal “sequence façade” + recurrence predicate used by the extractor plan.

  IMPORTANT (Lean 4.23-rc2 robustness):
  We import `Mathlib.Data.Complex.Basic` explicitly so `open Complex` is always legal,
  even if downstream files only import *this* module.

  Design choice (boundary-safe):
  We extend a Window-3 `w : Window 3` to an infinite sequence by padding zeros
  beyond index 2. This matches the boundary semantics of `toeplitzL 2` on `Fin 3`.
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Zero-padded infinite sequence associated to a Window-3. -/
def padSeq3 (w : Window 3) : ℕ → ℂ
  | 0 => w 0
  | 1 => w 1
  | 2 => w 2
  | _ => 0

@[simp] lemma padSeq3_zero (w : Window 3) : padSeq3 w 0 = w 0 := by
  simp [padSeq3]

@[simp] lemma padSeq3_one (w : Window 3) : padSeq3 w 1 = w 1 := by
  simp [padSeq3]

@[simp] lemma padSeq3_two (w : Window 3) : padSeq3 w 2 = w 2 := by
  simp [padSeq3]

/-- All indices ≥ 3 map to 0. (Convenient normal form for rewriting.) -/
@[simp] lemma padSeq3_succ_succ_succ (w : Window 3) (n : ℕ) :
    padSeq3 w (Nat.succ (Nat.succ (Nat.succ n))) = 0 := by
  simp [padSeq3]

/-- Order-2 recurrence predicate with coefficients `JetQuotOp.aRk1 s 0,1,2`. -/
def JetQuotRec2 (s : OffSeed Xi) (J : ℕ → ℂ) : Prop :=
  ∀ n : ℕ,
    (JetQuotOp.aRk1 s 0) * J n
      + (JetQuotOp.aRk1 s 1) * J (n + 1)
      + (JetQuotOp.aRk1 s 2) * J (n + 2) = 0

/-- Convenience bundle: the recurrence holds for the three AtOrder windows (padded). -/
structure XiJetQuotRec2AtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  h_w0At  : JetQuotRec2 s (padSeq3 (w0At m s))
  h_wp2At : JetQuotRec2 s (padSeq3 (wp2At m s))
  h_wp3At : JetQuotRec2 s (padSeq3 (wp3At m s))

end XiPacket
end Targets
end Hyperlocal
