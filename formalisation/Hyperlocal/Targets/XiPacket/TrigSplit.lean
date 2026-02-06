/-
  Hyperlocal/Targets/XiPacket/TrigSplit.lean

  Pure algebra: exponential → cosine/sine split.

  This version is robust to older Mathlib snapshots:
  • does NOT use `Complex.cos_ofReal` / `Complex.sin_ofReal`
  • avoids subtraction and avoids forcing `Real.cos/Real.sin` on the RHS
  • matches the multiplication ordering that `simp` produces (`sin * I`)
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/-- `exp((-x) * I) = cos x + -(sin x * I)` (works for complex `x`, no Real-cos needed). -/
lemma Complex.exp_neg_mul_I (x : ℂ) :
    Complex.exp ((-x) * Complex.I)
      =
    Complex.cos x + - (Complex.sin x * Complex.I) := by
  -- Start from `exp_mul_I (-x)` and simplify using trig parity.
  -- This will naturally produce the `sin * I` ordering (as in your error message).
  simpa [mul_assoc, add_assoc, sub_eq_add_neg] using
    (Complex.exp_mul_I (-x))

/--
Main split (robust form):

`exp(-(σ + i t) log p)
  = exp((-σ log p)) * (cos(t log p) + -(sin(t log p) * I))`

where `cos/sin` are `Complex.cos/Complex.sin` evaluated at a real-cast argument.
-/
lemma Complex.exp_neg_rho_log_eq (σ t p : ℝ) :
    Complex.exp ( -(((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log p : ℂ)) )
      =
    Complex.exp ((-σ * Real.log p : ℝ) : ℂ)
      * (Complex.cos ((t * Real.log p : ℝ) : ℂ)
          + - (Complex.sin ((t * Real.log p : ℝ) : ℂ) * Complex.I)) := by
  -- expand the exponent into real-part + imaginary-part*I
  have harg :
      -(((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log p : ℂ))
        =
      ((-σ * Real.log p : ℝ) : ℂ)
        + (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
    simp [mul_add, add_mul, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    ring_nf

  -- use exp_add and then apply the `exp_neg_mul_I` helper
  calc
    Complex.exp ( -(((σ : ℂ) + Complex.I * (t : ℂ)) * (Real.log p : ℂ)) )
        =
      Complex.exp (((-σ * Real.log p : ℝ) : ℂ)
        + (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I)) := by
          simpa [harg]
    _ =
      Complex.exp ((-σ * Real.log p : ℝ) : ℂ)
        * Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
          simpa using
            (Complex.exp_add
              ((-σ * Real.log p : ℝ) : ℂ)
              (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I))
    _ =
      Complex.exp ((-σ * Real.log p : ℝ) : ℂ)
        * (Complex.cos ((t * Real.log p : ℝ) : ℂ)
            + - (Complex.sin ((t * Real.log p : ℝ) : ℂ) * Complex.I)) := by
          -- note: `((-(t*log p)):ℂ) * I = (-((t*log p):ℂ)) * I`
          -- so the helper applies with `x := ((t*log p):ℝ):ℂ`.
          have := Complex.exp_neg_mul_I (((t * Real.log p : ℝ) : ℂ))
          -- rewrite LHS of `this` to match `exp (((-(t*log p)):ℂ) * I)`
          -- i.e. `(-x) * I` vs `((-(t*log p)):ℂ) * I`
          -- `simp` handles the coercions and negations.
          simpa [mul_assoc] using congrArg
            (fun z : ℂ => Complex.exp ((-σ * Real.log p : ℝ) : ℂ) * z)
            (by
              -- `this` has: exp((-x)*I)=...
              -- and our target factor is exp((-(t*log p))*I) with x = (t*log p)
              simpa [mul_assoc] using this)

end XiPacket
end Targets
end Hyperlocal
