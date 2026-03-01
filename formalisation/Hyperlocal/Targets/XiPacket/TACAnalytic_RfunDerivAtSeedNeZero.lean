/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_RfunDerivAtSeedNeZero.lean

  Robust bridge (NO dependency on an `Rfun` alias):

  Convert the *polynomial* nonvanishing fact
      (Polynomial.derivative (Rρk ρ 1)).eval ρ ≠ 0
  into the *complex-derivative of the scalar function*
      deriv (fun z => (Rρk ρ 1).eval z) ρ ≠ 0.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Hyperlocal.Factorization
import Hyperlocal.Targets.XiPacket.TACMinimalModel_QuartetDerivNeZero
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace TAC

/-- `deriv (fun z => p.eval z) = fun z => (p.derivative).eval z`. -/
lemma deriv_eval_eq_polynomial_derivative_eval (p : Polynomial ℂ) (z : ℂ) :
    deriv (fun w : ℂ => p.eval w) z = (Polynomial.derivative p).eval z := by
  -- This lemma exists in your environment if `Deriv.Polynomial` is imported.
  -- On most mathlib snapshots it's named `Polynomial.deriv_eval`.
  simpa using (Polynomial.deriv_eval (p := p) z)

/--
**Simple-root bridge at the seed (k = 1), no `Rfun` needed.**
-/
theorem deriv_Rρk_eval_at_seed_ne_zero (s : Hyperlocal.OffSeed Xi) :
    deriv (fun w : ℂ => (Hyperlocal.Factorization.Rρk s.ρ 1).eval w) s.ρ ≠ 0 := by
  -- polynomial fact already proved in your repo
  have hpoly :
      (Polynomial.derivative (Hyperlocal.Factorization.Rρk s.ρ 1)).eval s.ρ ≠ 0 :=
    Rρk_one_deriv_eval_seed_ne_zero (s := s)

  -- rewrite the LHS derivative into the polynomial-derivative evaluation
  have hbridge :
      deriv (fun w : ℂ => (Hyperlocal.Factorization.Rρk s.ρ 1).eval w) s.ρ
        =
      (Polynomial.derivative (Hyperlocal.Factorization.Rρk s.ρ 1)).eval s.ρ := by
    simpa using
      (deriv_eval_eq_polynomial_derivative_eval
        (p := Hyperlocal.Factorization.Rρk s.ρ 1) (z := s.ρ))

  -- conclude
  simpa [hbridge] using hpoly

end TAC

end XiPacket
end Targets
end Hyperlocal
