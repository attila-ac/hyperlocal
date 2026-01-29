/-
  Hyperlocal/Transport/JetWindow.lean

  Stage–3 scaffolding: the truncated jet “window” object and the manuscript’s
  `T`-notation landing in Lean.

  Engineering choices:
  • The underlying finite window type already exists as `Transport.Window`.
  • Toeplitz transport operators exist as `toeplitzR/toeplitzL` with the parity
    intertwiner lemma in `TACToeplitz.lean`.
  • This file just provides stable names and light wrappers so later files can
    talk “jet window + transport operator” without importing the whole Toeplitz
    stack each time.

  No axioms; no analytic claims here.
-/

import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Transport.ToeplitzInterface
import Hyperlocal.Transport.ToeplitzLinear

noncomputable section

namespace Hyperlocal
namespace Transport

/-- Truncated jet window of length `n+1` (coeff vector). -/
abbrev JetWindow (n : ℕ) : Type := Window (n + 1)

/-- Manuscript `T` operator: right/forward Toeplitz transport on a jet window. -/
abbrev T (n : ℕ) (coeffs : ℕ → ℂ) : EndW n := toeplitzR n coeffs

/-- Manuscript left/backward transport. -/
abbrev Tleft (n : ℕ) (coeffs : ℕ → ℂ) : EndW n := toeplitzL n coeffs

/-- Parity intertwines the manuscript `T` operator into the left transport. -/
theorem parityₗ_comp_T (n : ℕ) (coeffs : ℕ → ℂ) :
    (parityₗ n).comp (T n coeffs) = (Tleft n coeffs).comp (parityₗ n) := by
  simpa [T, Tleft] using parityₗ_comp_toeplitzR (n := n) (coeffs := coeffs)

/-- Trivial “T is shift-generated” witness (by definition). -/
theorem T_shiftGenerated (n : ℕ) (coeffs : ℕ → ℂ) :
    ShiftGenerated n (shiftRₗ n) (T n coeffs) :=
  toeplitzR_shiftGenerated (n := n) (coeffs := coeffs)

end Transport
end Hyperlocal
