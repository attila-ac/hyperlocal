import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation

open Matrix

-- Column vectors of length 4.
abbrev Jet4 := Fin 4 → ℂ

-- Concrete 4×4 almost–diagonal matrix.
def M4 (w : Jet4) (c10 c32 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![w 0,  0,   0,   0],
    ![c10,  w 1, 0,   0],
    ![0,    0,   w 2, 0],
    ![0,    0,   c32, w 3]]

-- Helper lemmas to simplify vecHead/vecTail noise.
@[simp] lemma vecHead0 (x : Jet4) : vecHead x = x 0 := rfl
@[simp] lemma vecHead1 (x : Jet4) : vecHead (vecTail x) = x 1 := rfl
@[simp] lemma vecHead2 (x : Jet4) : vecHead (vecTail (vecTail x)) = x 2 := rfl
@[simp] lemma vecHead3 (x : Jet4) : vecHead (vecTail (vecTail (vecTail x))) = x 3 := rfl

-- Closed form for mulVec.
lemma mulVec_M4 (w : Jet4) (c10 c32 : ℂ) (x : Jet4) :
    (M4 w c10 c32).mulVec x =
      ![ w 0 * x 0,
         c10 * x 0 + w 1 * x 1,
         w 2 * x 2,
         c32 * x 2 + w 3 * x 3 ] := by
  funext i
  fin_cases i <;>
    simp [M4, Matrix.mulVec, Fin.sum_univ_four]

-- If all diagonal entries are nonzero, then ker(M4) = {0}.
theorem kernel_M4_trivial
    (w : Jet4) (c10 c32 : ℂ)
    (hW : ∀ i : Fin 4, w i ≠ 0)
    {x : Jet4} (hx : (M4 w c10 c32).mulVec x = 0) :
    x = 0 := by
  have h0 : w 0 * x 0 = 0 := by
    have := congrArg (fun v => v 0) hx
    simpa [mulVec_M4] using this
  have hx0 : x 0 = 0 := by
    rcases (mul_eq_zero.mp h0) with hw0 | hx0
    · exact (hW 0 hw0).elim
    · exact hx0
  have h1 : c10 * x 0 + w 1 * x 1 = 0 := by
    have := congrArg (fun v => v 1) hx
    simpa [mulVec_M4] using this
  have hx1 : x 1 = 0 := by
    have : w 1 * x 1 = 0 := by simpa [hx0, add_comm] using h1
    rcases (mul_eq_zero.mp this) with hw1 | hx1
    · exact (hW 1 hw1).elim
    · exact hx1
  have h2 : w 2 * x 2 = 0 := by
    have := congrArg (fun v => v 2) hx
    simpa [mulVec_M4] using this
  have hx2 : x 2 = 0 := by
    rcases (mul_eq_zero.mp h2) with hw2 | hx2
    · exact (hW 2 hw2).elim
    · exact hx2
  have h3 : c32 * x 2 + w 3 * x 3 = 0 := by
    have := congrArg (fun v => v 3) hx
    simpa [mulVec_M4] using this
  have hx3 : x 3 = 0 := by
    have : w 3 * x 3 = 0 := by simpa [hx2, add_comm] using h3
    rcases (mul_eq_zero.mp this) with hw3 | hx3
    · exact (hW 3 hw3).elim
    · exact hx3
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3]

end Cancellation
end Hyperlocal

end
