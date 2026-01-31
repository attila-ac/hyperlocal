/-
  Hyperlocal/Targets/XiTransportOp.lean

  Concrete Toeplitz/shift-generated transport operator for the target `Xi`.

  We eliminate the “identification lemma” by *defining* the operator in Toeplitz form.
-/

import Hyperlocal.Targets.XiTransportToeplitz
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiTransport

open scoped Real
open Hyperlocal.Transport

/-- Real translation offset from the critical line. -/
def delta (s : Hyperlocal.OffSeed Xi) : ℝ :=
  s.ρ.re - (1 / 2 : ℝ)

/-- Toeplitz coefficients for truncated Taylor transport: δ^k / k!. -/
def shiftCoeff (δ : ℝ) : ℕ → ℂ :=
  fun k => ((δ : ℂ) ^ k) / (Nat.factorial k : ℂ)

/--
Concrete transport operator on jet windows:
Toeplitz right-convolution by the coefficient stencil δ^k/k!.
-/
def XiTransportOp (n : ℕ) (s : Hyperlocal.OffSeed Xi) : EndW n :=
  toeplitzR n (shiftCoeff (delta s))

/-- The identification lemma is now `rfl`. -/
theorem XiTransportOp_isToeplitz (n : ℕ) (s : Hyperlocal.OffSeed Xi) :
    IsToeplitz (XiTransportOp := XiTransportOp) n s := by
  refine ⟨shiftCoeff (delta s), rfl⟩

/-- Shift-generated (“stencil”) form is immediate. -/
theorem XiTransportOp_shiftGenerated {n : ℕ} {s : Hyperlocal.OffSeed Xi} :
    ShiftGenerated n (shiftRₗ n) (XiTransportOp n s) := by
  exact shiftGenerated_of_isToeplitz (XiTransportOp := XiTransportOp)
    (n := n) (s := s) (XiTransportOp_isToeplitz (n := n) (s := s))

/-- Parity intertwining consequence in the exact normal form you isolated. -/
theorem parityₗ_comp_XiTransportOp {n : ℕ} {s : Hyperlocal.OffSeed Xi} :
    ∃ coeffs : ℕ → ℂ,
      (parityₗ n).comp (XiTransportOp n s)
        = (toeplitzL n coeffs).comp (parityₗ n) := by
  exact parityₗ_comp_of_isToeplitz (XiTransportOp := XiTransportOp)
    (n := n) (s := s) (XiTransportOp_isToeplitz (n := n) (s := s))

end XiTransport
end Targets
end Hyperlocal
