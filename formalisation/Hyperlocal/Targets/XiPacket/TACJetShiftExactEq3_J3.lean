/-
  Hyperlocal/Targets/XiPacket/TACJetShiftExactEq3_J3.lean

  Goal: (eventually) discharge JetShiftExactEq 3 by quotient-ring semantics in
  J3 = ℂ[w]/(w^3).

  CURRENT STATUS (important):
    `JetShiftExactEq` (in TACTransportTruncated_JetQuot.lean) is *not* the quotient statement;
    it is an equality in ℂ of derivatives at (z+δ) against a truncated transport window.
    That equality is NOT true for a general differentiable/entire function.

    So: this file should *not* claim “Differentiable ⇒ JetShiftExactEq”.
    Instead it packages:
      - the Mathlib Taylor lemma you will use, and
      - a clean “if the knob holds, then you can use it” hook.
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_Algebra
import Hyperlocal.Targets.XiPacket.TACTransportTruncated
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuot

import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex
open scoped BigOperators

/--
A minimal “order-2 jet polynomial” in J3 using ordinary derivatives.

(When you switch to your project’s `iteratedDeriv`/`cderivIter` API, replace these.)
-/
def jetCoeff0 (f : ℂ → ℂ) (z : ℂ) : ℂ := f z
def jetCoeff1 (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv f z
def jetCoeff2 (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv (deriv f) z

/-- The J3-valued order-2 jet polynomial at z: a0 + a1*w + (a2/2)*w^2. -/
def J3Jet2 (f : ℂ → ℂ) (z : ℂ) : J3 :=
  J3.jet2 (jetCoeff0 f z) (jetCoeff1 f z) ((jetCoeff2 f z) / (2 : ℂ))

/--
Mathlib lemma you will use (your grep confirms it exists):

`Complex.taylorSeries_eq_of_entire'`:
  ∑' n, (n!)⁻¹ * iteratedDeriv n f c * (z - c)^n = f z
for entire/differentiable `f : ℂ → ℂ`.
-/
lemma taylorSeries_eq_of_entire'_at
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) :
        (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) * iteratedDeriv n f c * (z - c) ^ n) = f z := by
  simpa using (Complex.taylorSeries_eq_of_entire' (f := f) hf (c := c) (z := z))

/--
Usable hook today:

If you assume the single knob `h : JetShiftExactEq 3 f z δ`, you can extract the
coordinate equality at a given `j`.

(Explicit `h` avoids the parser issue you’re seeing with `[...]` binders.)
-/
theorem jetShiftExactEq3_use
    (f : ℂ → ℂ) (z δ : ℂ) (h : JetShiftExactEq 3 f z δ) :
    ∀ j : Fin 3, cderivIter j.1 f (z + δ) = transport 3 δ (jetVec 3 f z) j := by
  intro j
  simpa [jetVec] using (h.shift j)

end TAC
end XiPacket
end Targets
end Hyperlocal
