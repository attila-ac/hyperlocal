import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation

/-- A length-6 jet (first six Taylor coefficients). -/
abbrev Jet6 := Fin 6 → ℂ

/-- A toy diagonal “constraint” (hard-coded for 6 entries). -/
def diagScale (A t : ℝ) (i : Fin 6) : ℂ :=
  match i.val with
  | 0 => (1 : ℂ)
  | 1 => (2 : ℂ) * Complex.I * (t : ℂ)
  | 2 => (1 : ℂ) - (2 : ℂ) * (A : ℂ)
  | 3 => ((2 : ℂ) * Complex.I * (t : ℂ)) * ((1 : ℂ) - (2 : ℂ) * (A : ℂ))
  | 4 => (1 : ℂ)
  | _ => (1 : ℂ)

/-- Apply the diagonal to a jet. -/
def applyM (A t : ℝ) (x : Jet6) : Jet6 :=
  fun i => diagScale A t i * x i

/-- Kernel triviality for the toy diagonal: if all diagonal entries are nonzero,
    the only solution of `applyM A t x = 0` is `x = 0`. -/
theorem kernel_trivial
    (A t : ℝ)
    (h_nonzero : ∀ i : Fin 6, diagScale A t i ≠ 0)
    {x : Jet6}
    (hx : applyM A t x = 0) :
    x = 0 := by
  -- To prove the vector `x` is zero, we prove each of its components is zero.
  ext i
  -- Get the component-wise equation from the main hypothesis `hx`.
  have h_comp_eq : diagScale A t i * x i = 0 := by
    -- `funext_iff.mp hx` converts the function equality `hx` to a component-wise statement.
    exact funext_iff.mp hx i
  -- `mul_eq_zero.mp` splits `a * b = 0` into `a = 0 ∨ b = 0`.
  -- `.resolve_left` then uses our hypothesis `h_nonzero` to prove the left side can't be zero.
  -- This leaves `x i = 0` as the only possibility.
  exact (mul_eq_zero.mp h_comp_eq).resolve_left (h_nonzero i)

end Cancellation
end Hyperlocal

end section
