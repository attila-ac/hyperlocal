/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientShiftedSequenceAtOrderDefs.lean

  Step 1 (support file):
  A tiny “shifted sequence” façade for AtOrder windows.

  Provides:
    shiftSeq3 m w : ℕ → ℂ
  embedding a Window-3 at indices m..m+2 and 0 elsewhere,
  plus AtOrder specializations and simp lemmas.

  Cycle-safe: defs + simp lemmas only.
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Embed a `Window 3` as a shifted ℕ-sequence supported on indices `m, m+1, m+2`.
Outside that range the sequence is 0.
-/
def shiftSeq3 (m : ℕ) (w : Window 3) : ℕ → ℂ :=
  fun n => if h : m ≤ n then padSeq3 w (n - m) else 0

@[simp] lemma shiftSeq3_of_lt {m n : ℕ} {w : Window 3} (h : n < m) :
    shiftSeq3 m w n = 0 := by
  simp [shiftSeq3, Nat.not_le_of_gt h]

@[simp] lemma shiftSeq3_of_eq_add (m i : ℕ) (w : Window 3) :
    shiftSeq3 m w (m + i) = padSeq3 w i := by
  -- `if m ≤ m+i` then reduce `(m+i) - m` to `i`.
  simp [shiftSeq3, Nat.le_add_right, Nat.add_sub_cancel_left]

@[simp] lemma shiftSeq3_at (m : ℕ) (w : Window 3) :
    shiftSeq3 m w m = w 0 := by
  simpa [padSeq3] using (shiftSeq3_of_eq_add (m := m) (i := 0) (w := w))

@[simp] lemma shiftSeq3_succ (m : ℕ) (w : Window 3) :
    shiftSeq3 m w (m + 1) = w 1 := by
  simpa [padSeq3] using (shiftSeq3_of_eq_add (m := m) (i := 1) (w := w))

@[simp] lemma shiftSeq3_succ_succ (m : ℕ) (w : Window 3) :
    shiftSeq3 m w (m + 2) = w 2 := by
  simpa [padSeq3] using (shiftSeq3_of_eq_add (m := m) (i := 2) (w := w))

/-- Useful normal form: shifting by 0 is definitional padding. -/
@[simp] lemma shiftSeq3_zero (w : Window 3) :
    shiftSeq3 0 w = padSeq3 w := by
  funext n
  cases n with
  | zero =>
      simp [shiftSeq3, padSeq3]
  | succ n =>
      -- `0 ≤ succ n` is true, so reduce to `padSeq3 w (succ n - 0)`.
      simpa [shiftSeq3, padSeq3] using (by
        -- `Nat.succ n - 0 = Nat.succ n`
        simp [Nat.succ_sub (Nat.zero_le _)])

/-- Shifted sequence associated to the transported jet window `w0At m s`. -/
def Jw0At (m : ℕ) (s : OffSeed Xi) : ℕ → ℂ :=
  shiftSeq3 m (w0At m s)

/-- Shifted sequence associated to the prime window `wp2At m s`. -/
def Jwp2At (m : ℕ) (s : OffSeed Xi) : ℕ → ℂ :=
  shiftSeq3 m (wp2At m s)

/-- Shifted sequence associated to the prime window `wp3At m s`. -/
def Jwp3At (m : ℕ) (s : OffSeed Xi) : ℕ → ℂ :=
  shiftSeq3 m (wp3At m s)

/-!
Simp lemmas: each AtOrder window is the restriction of its shifted sequence.
-/

@[simp] lemma Jw0At_add (m i : ℕ) (s : OffSeed Xi) :
    Jw0At m s (m + i) = padSeq3 (w0At m s) i := by
  simp [Jw0At, shiftSeq3_of_eq_add]

@[simp] lemma Jwp2At_add (m i : ℕ) (s : OffSeed Xi) :
    Jwp2At m s (m + i) = padSeq3 (wp2At m s) i := by
  simp [Jwp2At, shiftSeq3_of_eq_add]

@[simp] lemma Jwp3At_add (m i : ℕ) (s : OffSeed Xi) :
    Jwp3At m s (m + i) = padSeq3 (wp3At m s) i := by
  simp [Jwp3At, shiftSeq3_of_eq_add]

end XiPacket
end Targets
end Hyperlocal
