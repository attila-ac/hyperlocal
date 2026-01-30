/-
  Hyperlocal/Transport/TACExtraction.lean

  Stage-3 scaffolding: extraction interface.

  From an off-critical seed s : OffSeed H, build a prime-indexed scalar test Psi_s(p,t)
  and extracted data (A,B,κ) such that:
    • A,B are even; κ ≠ 0
    • Psi_s(p,t) matches the canonical PhiPrime form
    • transported symmetry forces oddPart(Psi_s(2,·)) t0 = 0 and oddPart(Psi_s(3,·)) t0 = 0
      where t0 := Im(s.ρ).

  No axioms here: Stage3System H is a Prop (Nonempty of the witness structure).
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.ScalarFunctional
import Hyperlocal.Transport.TAC
import Hyperlocal.Cancellation.PrimeWitnessParity
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped Real
open Hyperlocal.Cancellation.PrimeWitness
open Hyperlocal.Cancellation.PrimeWitness (oddPart)

/-- Prime-indexed scalar test: p ↦ (t ↦ ℝ). -/
abbrev PrimeTest : Type := ℕ → ℝ → ℝ

/-- Extracted TAC coefficient package (output of the extraction stage). -/
structure TACData where
  A  : ℝ → ℝ
  B  : ℝ → ℝ
  κ  : ℝ
  hA : Hyperlocal.Transport.TAC.EvenF A
  hB : Hyperlocal.Transport.TAC.EvenF B
  hκ : κ ≠ 0

/-- Stage-3 witness bundle: functions + proofs, living in `Type`. -/
structure Stage3SystemData (H : ℂ → ℂ) where
  test  : Hyperlocal.OffSeed H → PrimeTest
  tac   : Hyperlocal.OffSeed H → TACData
  hMatch :
    ∀ (s : Hyperlocal.OffSeed H) (p : ℕ) (t : ℝ),
      test s p t =
        Hyperlocal.Transport.TAC.PhiPrime
          (tac s).A (tac s).B (fun _ => (tac s).κ) p t
  hOdd2 :
    ∀ (s : Hyperlocal.OffSeed H),
      oddPart (test s 2) s.ρ.im = 0
  hOdd3 :
    ∀ (s : Hyperlocal.OffSeed H),
      oddPart (test s 3) s.ρ.im = 0

/-- Stage-3 system as a Prop: there exists a witness bundle satisfying the contract. -/
def Stage3System (H : ℂ → ℂ) : Prop :=
  Nonempty (Stage3SystemData H)

/-- Compressed: odd-part vanishing for canonical PhiPrime at primes 2 and 3. -/
def OffSeedTACZeros2_3 (H : ℂ → ℂ) : Prop :=
  ∀ s : Hyperlocal.OffSeed H,
    ∃ (A B : ℝ → ℝ) (κ : ℝ),
      Hyperlocal.Transport.TAC.EvenF A ∧
      Hyperlocal.Transport.TAC.EvenF B ∧
      κ ≠ 0 ∧
      oddPart (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 2) s.ρ.im = 0 ∧
      oddPart (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 3) s.ρ.im = 0

/-- Stage3System H implies OffSeedTACZeros2_3 H. -/
theorem offSeedTACZeros2_3_of_stage3System
    {H : ℂ → ℂ} (hs : Stage3System H) : OffSeedTACZeros2_3 H := by
  rcases hs with ⟨sys⟩
  intro s
  refine ⟨(sys.tac s).A, (sys.tac s).B, (sys.tac s).κ,
          (sys.tac s).hA, (sys.tac s).hB, (sys.tac s).hκ, ?_, ?_⟩
  · -- p = 2
    have hfun :
        sys.test s 2 =
          Hyperlocal.Transport.TAC.PhiPrime
            (sys.tac s).A (sys.tac s).B (fun _ => (sys.tac s).κ) 2 := by
      funext t
      simpa using sys.hMatch s 2 t
    have h0 : oddPart (sys.test s 2) s.ρ.im = 0 := sys.hOdd2 s
    rw [hfun] at h0
    exact h0
  · -- p = 3
    have hfun :
        sys.test s 3 =
          Hyperlocal.Transport.TAC.PhiPrime
            (sys.tac s).A (sys.tac s).B (fun _ => (sys.tac s).κ) 3 := by
      funext t
      simpa using sys.hMatch s 3 t
    have h0 : oddPart (sys.test s 3) s.ρ.im = 0 := sys.hOdd3 s
    rw [hfun] at h0
    exact h0

end Transport
end Hyperlocal
