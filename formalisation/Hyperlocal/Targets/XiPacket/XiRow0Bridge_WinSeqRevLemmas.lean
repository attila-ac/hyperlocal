/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WinSeqRevLemmas.lean

  Small, cycle-safe definitional lemmas about `winSeqRev`.

  These are used as the first ingredient for "shift/reindex" arguments relating
  reverse convolution coefficients at n=3,4,5 to Toeplitz row constraints.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

@[simp] lemma winSeqRev_zero (w : Transport.Window 3) :
    winSeqRev w 0 = w ⟨2, by decide⟩ := rfl

@[simp] lemma winSeqRev_one (w : Transport.Window 3) :
    winSeqRev w 1 = w ⟨1, by decide⟩ := rfl

@[simp] lemma winSeqRev_two (w : Transport.Window 3) :
    winSeqRev w 2 = w ⟨0, by decide⟩ := rfl

@[simp] lemma winSeqRev_succ_succ_succ (w : Transport.Window 3) (n : ℕ) :
    winSeqRev w (n + 3) = 0 := by
  -- by cases on the definition; the `_` branch is `0`
  cases n <;> rfl

/-- Convenient form: if `3 ≤ n` then `winSeqRev w n = 0`. -/
lemma winSeqRev_eq_zero_of_ge_three (w : Transport.Window 3) {n : ℕ} (hn : 3 ≤ n) :
    winSeqRev w n = 0 := by
  -- write n = k + 3
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (winSeqRev_succ_succ_succ (w := w) k)

namespace WinSeqRevLemmasExport
export _root_.Hyperlocal.Targets.XiPacket
  (winSeqRev_zero winSeqRev_one winSeqRev_two
   winSeqRev_succ_succ_succ winSeqRev_eq_zero_of_ge_three)
end WinSeqRevLemmasExport

end XiPacket
end Targets
end Hyperlocal
