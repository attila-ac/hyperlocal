/-
  Hyperlocal/Targets/XiOffSeedTACZeros2_3Proof.lean

  FINAL semantic cliff (v4.0):

  To make the last step minimal, we factor it as:

    xi_twoPrimeSine : for an off-seed s, produce κ ≠ 0 with
      κ * sin(t log 2) = 0  and  κ * sin(t log 3) = 0,  where t = s.ρ.im.

  Then the required TAC oddPart equalities are immediate using
  TAC.oddPart_PhiPrime_constC (even-part cancels automatically).
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.TAC
import Hyperlocal.Transport.TACExtraction
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Cancellation.PrimeWitness

/-- Notation match. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/--
The *only* ξ-specific lemma you still owe.

Interpretation: from your concrete ξ-transport / finite-window recurrence,
extract a nonzero κ forcing the two-prime phase-lock constraints
at t = s.ρ.im.
-/
theorem xi_twoPrimeSine (s : Hyperlocal.OffSeed Xi) :
    ∃ κ : ℝ, κ ≠ 0 ∧
      κ * Real.sin (s.ρ.im * Real.log 2) = 0 ∧
      κ * Real.sin (s.ρ.im * Real.log 3) = 0 := by
  -- TODO: your ξ window recurrence / stencil extraction goes here.
  sorry

/--
Main target: OffSeedTACZeros2_3 for ξ.

This is now *pure glue*: choose A = 0, B = 0, and reuse xi_twoPrimeSine.
-/
theorem xi_offSeedTACZeros2_3 : Hyperlocal.Transport.OffSeedTACZeros2_3 Xi := by
  intro s
  rcases xi_twoPrimeSine (s := s) with ⟨κ, hκ, h2, h3⟩

  -- Evenness facts for the chosen A,B = 0
  have hA0 : Hyperlocal.Transport.TAC.EvenF (fun _ : ℝ => (0 : ℝ)) := by
    intro u; simp [Hyperlocal.Transport.TAC.EvenF]
  have hB0 : Hyperlocal.Transport.TAC.EvenF (fun _ : ℝ => (0 : ℝ)) := by
    intro u; simp [Hyperlocal.Transport.TAC.EvenF]

  refine ⟨(fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (0 : ℝ)), κ, hA0, hB0, hκ, ?_, ?_⟩

  · -- p = 2
    calc
      oddPart
          (Hyperlocal.Transport.TAC.PhiPrime
            (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => κ) (2 : ℕ))
          s.ρ.im
          = PhiShape κ s.ρ.im (2 : ℕ) := by
              simpa using
                (Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
                  (A := fun _ : ℝ => (0 : ℝ))
                  (B := fun _ : ℝ => (0 : ℝ))
                  (κ := κ) (p := (2 : ℕ))
                  hA0 hB0 (t := s.ρ.im))
      _ = 0 := by
              simpa [PhiShape] using h2

  · -- p = 3
    calc
      oddPart
          (Hyperlocal.Transport.TAC.PhiPrime
            (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => κ) (3 : ℕ))
          s.ρ.im
          = PhiShape κ s.ρ.im (3 : ℕ) := by
              simpa using
                (Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
                  (A := fun _ : ℝ => (0 : ℝ))
                  (B := fun _ : ℝ => (0 : ℝ))
                  (κ := κ) (p := (3 : ℕ))
                  hA0 hB0 (t := s.ρ.im))
      _ = 0 := by
              simpa [PhiShape] using h3

end Targets
end Hyperlocal
