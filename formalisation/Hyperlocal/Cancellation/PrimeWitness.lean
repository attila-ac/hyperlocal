/-
  Hyperlocal/Cancellation/PrimeWitness.lean

  Minimal Lean skeleton for the finite-prime witness.

  Downstream you will engineer a scalar functional L such that a prime-indexed
  scalar test has the form κ * sin(t * log p). If κ ≠ 0 and t ≠ 0 then at least
  one of p=2 or p=3 witnesses non-vanishing.

  The only arithmetic bottleneck is isolated as an axiom for now:
    sin(t log 2)=0 ∧ sin(t log 3)=0  →  t=0.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open scoped Real

/-- Minimal witness shape: κ * sin(t * log p). -/
def PhiShape (κ t : ℝ) (p : ℕ) : ℝ :=
  κ * Real.sin (t * Real.log (p : ℝ))

/-- Arithmetic bottleneck (postponed): two-base phase lock forces t = 0. -/
axiom two_prime_phase_lock (t : ℝ) :
  Real.sin (t * Real.log (2 : ℝ)) = 0 ∧
  Real.sin (t * Real.log (3 : ℝ)) = 0 → t = 0

/--
If κ ≠ 0 and t ≠ 0, then not both Φ(2) and Φ(3) vanish.
Equivalently: Φ(2) ≠ 0 ∨ Φ(3) ≠ 0.
-/
theorem finite_prime_witness_2_3
    {κ t : ℝ} (hκ : κ ≠ 0) (ht : t ≠ 0) :
    PhiShape κ t 2 ≠ 0 ∨ PhiShape κ t 3 ≠ 0 := by
  by_contra hboth
  push_neg at hboth
  have hPhi2 : PhiShape κ t 2 = 0 := hboth.1
  have hPhi3 : PhiShape κ t 3 = 0 := hboth.2

  have hsin2 : Real.sin (t * Real.log (2 : ℝ)) = 0 := by
    have h0 : κ * Real.sin (t * Real.log (2 : ℝ)) = 0 := by
      simpa [PhiShape] using hPhi2
    have hOr := mul_eq_zero.mp h0
    cases hOr with
    | inl hk0 => exact (False.elim (hκ hk0))
    | inr hsin => exact hsin

  have hsin3 : Real.sin (t * Real.log (3 : ℝ)) = 0 := by
    have h0 : κ * Real.sin (t * Real.log (3 : ℝ)) = 0 := by
      simpa [PhiShape] using hPhi3
    have hOr := mul_eq_zero.mp h0
    cases hOr with
    | inl hk0 => exact (False.elim (hκ hk0))
    | inr hsin => exact hsin

  have : t = 0 := two_prime_phase_lock t ⟨hsin2, hsin3⟩
  exact ht this

end PrimeWitness
end Cancellation
end Hyperlocal
