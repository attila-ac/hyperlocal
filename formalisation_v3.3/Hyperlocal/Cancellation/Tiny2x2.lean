/-
  Tiny 2×2 almost–diagonal system with an off–diagonal bump.
  We prove: if the diagonal entries are nonzero, then ker(M) = {0}.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation   -- for ![ ... ] notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Hyperlocal
namespace Cancellation

open Matrix

/-- Column vectors of length 2. -/
abbrev Jet2 := Fin 2 → ℂ

/-- Pure diagonal: `diag2 a b = [[a, 0], [0, b]]`. -/
def diag2 (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![a, 0],
    ![0, b]]

/-- Single off–diagonal bump at (row 1, col 0): `[[0, 0], [c, 0]]`. -/
def bump10 (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 0],
    ![c, 0]]

/-- Almost–diagonal 2×2 matrix. -/
def M2 (a b c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diag2 a b + bump10 c

/-- Evaluate `(M2 a b c).mulVec x` coordinatewise. -/
lemma mulVec_M2 (a b c : ℂ) (x : Jet2) :
    (M2 a b c).mulVec x = ![a * x 0, c * x 0 + b * x 1] := by
  classical
  funext i
  fin_cases i <;>
    simp [M2, diag2, bump10, Matrix.mulVec]

/-- If `a ≠ 0` and `b ≠ 0`, then `ker (M2 a b c)` is trivial. -/
theorem kernel_M2_trivial {a b c : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    {x : Jet2} (hx : (M2 a b c).mulVec x = 0) :
    x = 0 := by
  classical
  -- Row 0 equation
  have h0eq : a * x 0 = 0 := by
    have := congrArg (fun v => v 0) hx
    simpa [mulVec_M2] using this
  have hx0 : x 0 = 0 := by
    rcases (mul_eq_zero.mp h0eq) with ha0 | h
    · exact (ha ha0).elim
    · exact h
  -- Row 1 equation
  have h1eq : c * x 0 + b * x 1 = 0 := by
    have := congrArg (fun v => v 1) hx
    simpa [mulVec_M2] using this
  have hb_x1 : b * x 1 = 0 := by simpa [hx0] using h1eq
  have hx1 : x 1 = 0 := by
    rcases (mul_eq_zero.mp hb_x1) with hb0 | h
    · exact (hb hb0).elim
    · exact h
  -- Conclude equality of functions `Fin 2 → ℂ`.
  funext i
  fin_cases i <;> simpa [hx0, hx1]

/-- Sanity: with `a = b = 1`, kernel is trivial for any `c`. -/
example (c : ℂ) (x : Jet2) (hx : (M2 1 1 c).mulVec x = 0) : x = 0 :=
  kernel_M2_trivial (by simp) (by simp) hx

end Cancellation
end Hyperlocal
