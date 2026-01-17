import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
open scoped BigOperators
noncomputable section

namespace Hyperlocal
namespace Cancellation

/-- Complex sequences indexed by natural numbers. -/
abbrev CSeq := ℕ → ℂ

/--
A recurrence specification:

* `L`   – order of the homogeneous part (how many previous terms appear).
* `a0`  – the leading scalar multiplying `b n`.
* `a j` – the coefficient function for shifts; we only use values at `j = 1..L`.
-/
structure RecSpec where
  L  : ℕ
  a0 : ℂ
  a  : ℕ → ℂ

namespace RecSpec

variable {R : RecSpec}

/-- Homogeneous RHS: `- ∑_{j=1..L} a(j) * b(n-j)` written with `Finset.range`. -/
def homRHS (R : RecSpec) (b : CSeq) (n : ℕ) : ℂ :=
  - (range R.L).sum (fun j => R.a (j+1) * b (n - (j+1)))

/-- Full RHS: homogeneous part + inhomogeneity `h n`. -/
def fullRHS (R : RecSpec) (h b : CSeq) (n : ℕ) : ℂ :=
  R.homRHS b n + h n

/--
The recurrence holds from a threshold `n0` if for all `n ≥ n0`:
`a0 * b n = fullRHS h b n`.
-/
def HoldsFrom (R : RecSpec) (h b : CSeq) (n0 : ℕ) : Prop :=
  ∀ ⦃n⦄, n ≥ n0 → R.a0 * b n = R.fullRHS h b n

/-- Default threshold is `n ≥ L`, so all shifts `n - (j+1)` are defined. -/
abbrev Holds (R : RecSpec) (h b : CSeq) : Prop := R.HoldsFrom h b R.L

/-- The homogeneous RHS vanishes if all `a(j)=0` on `j=1..L`. -/
lemma homRHS_zero_of_a_zero
    (R : RecSpec) (b : CSeq) (n : ℕ)
    (h0 : ∀ j, 1 ≤ j ∧ j ≤ R.L → R.a j = 0) :
    R.homRHS b n = 0 := by
  classical
  unfold homRHS
  have : (range R.L).sum (fun j => R.a (j+1) * b (n - (j+1))) = 0 := by
    refine Finset.sum_eq_zero ?hterm
    intro j hj
    have hlt : j < R.L := by simpa [Finset.mem_range] using hj
    have h1 : 1 ≤ j+1 := Nat.succ_le_succ (Nat.zero_le _)
    have h2 : j+1 ≤ R.L := Nat.succ_le_of_lt hlt
    have hz : R.a (j+1) = 0 := h0 (j+1) ⟨h1, h2⟩
    simp [hz]
  simp [this]

end RecSpec

/-- Handy zero sequence. -/
@[simp] def zeroSeq : CSeq := fun _ => (0 : ℂ)
@[simp] lemma zeroSeq_eval (n : ℕ) : zeroSeq n = 0 := rfl

/-
  Smokes (plain compile-time checks).
-/
section Smokes

  /-- If `a0 = 0` and all `a(j)=0`, then any `b` solves the recurrence with `h ≡ 0`. -/
  example (b : CSeq) :
      (let R : RecSpec := ⟨2, (0 : ℂ), fun _ => (0 : ℂ)⟩;
       R.Holds (zeroSeq) b) := by
    classical
    change (⟨2, (0 : ℂ), fun _ => (0 : ℂ)⟩ : RecSpec).Holds (zeroSeq) b
    intro n hn
    have hhom :
        (⟨2, (0 : ℂ), fun _ => (0 : ℂ)⟩ : RecSpec).homRHS b n = 0 := by
      refine RecSpec.homRHS_zero_of_a_zero
        (R := ⟨2, (0 : ℂ), fun _ => (0 : ℂ)⟩) (b := b) (n := n) ?_
      intro j hj; simp
    simp [RecSpec.fullRHS, hhom, zeroSeq]

  /-- With `b ≡ 0` and `h ≡ 0`, the recurrence holds for any `R`. -/
  example (R : RecSpec) :
      R.Holds (zeroSeq) (zeroSeq) := by
    classical
    intro n hn
    simp [RecSpec.fullRHS, RecSpec.homRHS, zeroSeq]

end Smokes

end Cancellation
end Hyperlocal
