/-
  Hyperlocal/Transport/PhaseLock2_3.lean

  Final step of the Transport split:

    OffSeedTACZeros2_3 H  →  OffSeedPhaseLock H

  i.e. once extraction has produced the PhiPrime form (A,B even, κ≠0) and shown
  oddPart vanishes at primes 2 and 3 for t0 = Im(ρ), we deduce:

      sin(t0 log 2)=0  and  sin(t0 log 3)=0

  Pure algebra using:
    • `Transport.TAC.oddPart_PhiPrime_constC`
    • `PrimeWitness.PhiShape`
    • `mul_eq_zero` and κ≠0
-/

import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Transport.TAC
import Hyperlocal.Cancellation.PrimeWitness

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped Real
open Hyperlocal.Cancellation.PrimeWitness
open Hyperlocal.Cancellation.PrimeWitness (oddPart)

/-- Helper: from κ≠0 and κ*sin(..)=0, deduce sin(..)=0. -/
lemma sin_zero_of_mul_sin_zero {κ x : ℝ} (hκ : κ ≠ 0) (h : κ * Real.sin x = 0) :
    Real.sin x = 0 := by
  have hOr := mul_eq_zero.mp h
  cases hOr with
  | inl hk0 => exact False.elim (hκ hk0)
  | inr hs0 => exact hs0

/--
Core phase-lock lemma:
from the compressed extracted constraints, deduce the sine equalities at 2 and 3.
-/
theorem offSeedPhaseLock_of_offSeedTACZeros2_3
    {H : ℂ → ℂ} (hZ : OffSeedTACZeros2_3 H) :
    OffSeedPhaseLock H := by
  intro s
  rcases hZ s with ⟨A, B, κ, hA, hB, hκ, hOdd2, hOdd3⟩
  refine ⟨κ, hκ, ?_, ?_⟩
  · -- sin(t log 2)=0
    have hRewrite :=
      Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
        (A := A) (B := B) (κ := κ) (p := 2) hA hB s.ρ.im
    -- rewrite hOdd2 into PhiShape=0 without simp loops
    have hPhi2 : PhiShape κ s.ρ.im 2 = 0 := by
      -- hOdd2 : oddPart (PhiPrime ...) t = 0
      -- hRewrite : oddPart (PhiPrime ...) t = PhiShape ...
      -- so rewrite at hOdd2:
      have htmp := hOdd2
      rw [hRewrite] at htmp
      exact htmp
    have hMul : κ * Real.sin (s.ρ.im * Real.log (2 : ℝ)) = 0 := by
      simpa [PhiShape] using hPhi2
    exact sin_zero_of_mul_sin_zero (κ := κ) (x := s.ρ.im * Real.log (2 : ℝ)) hκ hMul
  · -- sin(t log 3)=0
    have hRewrite :=
      Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
        (A := A) (B := B) (κ := κ) (p := 3) hA hB s.ρ.im
    have hPhi3 : PhiShape κ s.ρ.im 3 = 0 := by
      have htmp := hOdd3
      rw [hRewrite] at htmp
      exact htmp
    have hMul : κ * Real.sin (s.ρ.im * Real.log (3 : ℝ)) = 0 := by
      simpa [PhiShape] using hPhi3
    exact sin_zero_of_mul_sin_zero (κ := κ) (x := s.ρ.im * Real.log (3 : ℝ)) hκ hMul

/--
If you manage to prove `Stage3System H` (the real Transport math),
you automatically get the phase-lock contract used by OffSeedBridge.
-/
theorem offSeedPhaseLock_of_stage3System
    {H : ℂ → ℂ} (hs : Stage3System H) :
    OffSeedPhaseLock H :=
  offSeedPhaseLock_of_offSeedTACZeros2_3
    (hZ := offSeedTACZeros2_3_of_stage3System (H := H) hs)

end Transport
end Hyperlocal
Sc
