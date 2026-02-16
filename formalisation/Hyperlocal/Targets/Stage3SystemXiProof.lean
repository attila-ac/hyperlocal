/-
  Hyperlocal/Targets/Stage3SystemXiProof.lean

  Modular construction of Stage3System Xi.

  This file proves (constructively)  OffSeedPhaseLock Xi → Stage3System Xi,
  and composes to get NoOffSeed Xi.

  NOTE:
  This does NOT yet prove OffSeedPhaseLock Xi itself (that is the Toeplitz/TAC arm).
-/

import Hyperlocal.Targets.Stage3SystemXi
import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Transport.TAC
import Hyperlocal.Transport.OffSeedBridge
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets

open scoped Real
open Hyperlocal.Cancellation.PrimeWitness
open Hyperlocal.Cancellation.PrimeWitness (oddPart)

/-- OffSeedPhaseLock Xi implies Stage3System Xi (modular construction, no axioms). -/
theorem stage3System_xi_of_phaseLock
    (hlock : Hyperlocal.Transport.OffSeedPhaseLock (H := Xi)) :
    Hyperlocal.Transport.Stage3System (H := Xi) := by
  classical

  -- Choose κ(s) from the phase-lock witness.
  let κ : Hyperlocal.OffSeed Xi → ℝ := fun s => Classical.choose (hlock s)
  have hκspec :
      ∀ s : Hyperlocal.OffSeed Xi,
        κ s ≠ 0 ∧
        Real.sin (s.ρ.im * Real.log (2 : ℝ)) = 0 ∧
        Real.sin (s.ρ.im * Real.log (3 : ℝ)) = 0 := by
    intro s
    simpa [κ] using Classical.choose_spec (hlock s)

  -- Trivial even coefficients.
  let A0 : ℝ → ℝ := fun _ => 0
  let B0 : ℝ → ℝ := fun _ => 0

  have hA0 : Hyperlocal.Transport.TAC.EvenF A0 := by
    intro t
    simp [Hyperlocal.Transport.TAC.EvenF, A0]
  have hB0 : Hyperlocal.Transport.TAC.EvenF B0 := by
    intro t
    simp [Hyperlocal.Transport.TAC.EvenF, B0]

  -- Define the prime-indexed test ψ_s(p,t).
  let testFun : Hyperlocal.OffSeed Xi → Hyperlocal.Transport.PrimeTest :=
    fun s => fun p t =>
      Hyperlocal.Transport.TAC.PhiPrime A0 B0 (fun _ => κ s) p t

  -- Define the extracted TAC package.
  let tacFun : Hyperlocal.OffSeed Xi → Hyperlocal.Transport.TACData := fun s =>
    { A := A0
      B := B0
      κ := κ s
      hA := hA0
      hB := hB0
      hκ := (hκspec s).1 }

  -- Odd-part vanishing at p=2.
  have hOdd2 : ∀ s : Hyperlocal.OffSeed Xi,
      oddPart (testFun s 2) s.ρ.im = 0 := by
    intro s
    have h2 :=
      Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
        (A := A0) (B := B0) (κ := κ s) (p := 2) hA0 hB0 (t := s.ρ.im)
    calc
      oddPart (testFun s 2) s.ρ.im
          = PhiShape (κ s) s.ρ.im 2 := by
              simpa [testFun, A0, B0] using h2
      _ = 0 := by
              simp [PhiShape, (hκspec s).2.1]

  -- Odd-part vanishing at p=3.
  have hOdd3 : ∀ s : Hyperlocal.OffSeed Xi,
      oddPart (testFun s 3) s.ρ.im = 0 := by
    intro s
    have h3 :=
      Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
        (A := A0) (B := B0) (κ := κ s) (p := 3) hA0 hB0 (t := s.ρ.im)
    calc
      oddPart (testFun s 3) s.ρ.im
          = PhiShape (κ s) s.ρ.im 3 := by
              simpa [testFun, A0, B0] using h3
      _ = 0 := by
              simp [PhiShape, (hκspec s).2.2]

  -- Build the witness bundle.
  let sys : Hyperlocal.Transport.Stage3SystemData (H := Xi) :=
    { test := testFun
      tac := tacFun
      hMatch := by
        intro s p t
        rfl
      hOdd2 := hOdd2
      hOdd3 := hOdd3 }

  exact ⟨sys⟩

/-- Therefore, OffSeedPhaseLock Xi already yields the full endgame NoOffSeed Xi. -/
theorem noOffSeed_xi_of_phaseLock
    (hlock : Hyperlocal.Transport.OffSeedPhaseLock (H := Xi)) :
    Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed (H := Xi) := by
  exact noOffSeed_xi_of_stage3System
    (hs := stage3System_xi_of_phaseLock (hlock := hlock))

end Targets
end Hyperlocal
