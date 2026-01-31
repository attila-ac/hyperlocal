/-
  Hyperlocal/Transport/Stage3SystemOfPhaseLock.lean

  Constructor file (non-axiomatic):

    OffSeedPhaseLock(H)  →  Stage3System(H)

  by explicitly filling Stage3SystemData with:
    A(t) ≡ 0,  B(t) ≡ 0,  C(t) ≡ κ(s) (constant in t)
  and using oddPart_PhiPrime_constC + the phase-lock sine equalities at p=2,3.

  IMPORTANT: Stage3System is `Nonempty (Stage3SystemData H)`,
  so the final packaging is `exact ⟨sys⟩`.
-/

import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Transport.TAC
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped Real
open Hyperlocal.Cancellation.PrimeWitness
open Hyperlocal.Cancellation.PrimeWitness (oddPart)

/-- Core constructor: Phase-lock contract ⇒ Stage-3 system. -/
theorem stage3System_of_phaseLock
    {H : ℂ → ℂ} (hlock : OffSeedPhaseLock (H := H)) :
    Stage3System (H := H) := by
  classical

  -- Choose κ(s) from the phase-lock witness.
  let κ : Hyperlocal.OffSeed H → ℝ := fun s => Classical.choose (hlock s)
  have hκspec :
      ∀ s : Hyperlocal.OffSeed H,
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
    simp [A0]
  have hB0 : Hyperlocal.Transport.TAC.EvenF B0 := by
    intro t
    simp [B0]

  -- Define the prime-indexed test ψ_s(p,t).
  let testFun : Hyperlocal.OffSeed H → PrimeTest :=
    fun s => fun p t =>
      Hyperlocal.Transport.TAC.PhiPrime A0 B0 (fun _ => κ s) p t

  -- Define the extracted TAC package.
  let tacFun : Hyperlocal.OffSeed H → TACData := fun s =>
    { A := A0
      B := B0
      κ := κ s
      hA := hA0
      hB := hB0
      hκ := (hκspec s).1 }

  -- Odd-part vanishing at p=2.
  have hOdd2 : ∀ s : Hyperlocal.OffSeed H,
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
  have hOdd3 : ∀ s : Hyperlocal.OffSeed H,
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

  -- Build the 5-field witness bundle explicitly, then wrap into `Nonempty`.
  let sys : Stage3SystemData (H := H) :=
    { test := testFun
      tac := tacFun
      hMatch := by
        intro s p t
        rfl
      hOdd2 := hOdd2
      hOdd3 := hOdd3 }

  exact ⟨sys⟩

end Transport
end Hyperlocal
