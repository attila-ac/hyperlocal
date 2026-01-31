/-
  Hyperlocal/Targets/XiPhaseLock.lean

  v4.0/v4.1 target: derive `NoOffSeed Xi`.

  The only remaining semantic input is the Stage-3 coupling package
  `Stage3Bridge (H := Xi)`.
-/

import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Conclusion.OffSeedToTAC
import Hyperlocal.Transport.TAC
import Hyperlocal.Cancellation.PrimeWitness
import Hyperlocal.Targets.RiemannXi
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPhaseLock

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.TAC
open Hyperlocal.Cancellation.PrimeWitness
open Hyperlocal.Conclusion.OffSeedToTAC

/-- The chosen Xi target. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/--
Stage-3 coupling package for Xi.

This is the single remaining semantic item: from any off-critical zero of Xi,
extract `A`, `B` and a nonzero `κ` for which the TAC odd-part vanishes at primes
2 and 3.
-/
axiom stage3Bridge_Xi : Stage3Bridge Xi

/--
(Optionally useful) Extract the explicit two-prime phase-lock from the Stage-3 bridge:
`sin(t log 2) = 0` and `sin(t log 3) = 0`.
-/
theorem offSeedPhaseLock_Xi : OffSeedPhaseLock (H := Xi) := by
  intro s
  rcases stage3Bridge_Xi.bridge s with ⟨A, B, κ, hκ, hTAC⟩
  rcases hTAC with ⟨hA, hB, h2, h3⟩
  refine ⟨κ, hκ, ?_, ?_⟩
  · -- p = 2
    have hodd2 :=
      oddPart_PhiPrime_constC (A := A) (B := B) (κ := κ) (p := 2) hA hB (t := s.ρ.im)
    have hshape2 : PhiShape κ s.ρ.im 2 = 0 := by
      calc
        PhiShape κ s.ρ.im 2
            = oddPart (PhiPrime A B (fun _ => κ) 2) s.ρ.im := by
                simpa using hodd2.symm
        _ = 0 := h2
    have hmul : κ * Real.sin (s.ρ.im * Real.log (2 : ℝ)) = 0 := by
      simpa [PhiShape] using hshape2
    rcases mul_eq_zero.mp hmul with hk0 | hsin
    · exact False.elim (hκ hk0)
    · exact hsin
  · -- p = 3
    have hodd3 :=
      oddPart_PhiPrime_constC (A := A) (B := B) (κ := κ) (p := 3) hA hB (t := s.ρ.im)
    have hshape3 : PhiShape κ s.ρ.im 3 = 0 := by
      calc
        PhiShape κ s.ρ.im 3
            = oddPart (PhiPrime A B (fun _ => κ) 3) s.ρ.im := by
                simpa using hodd3.symm
        _ = 0 := h3
    have hmul : κ * Real.sin (s.ρ.im * Real.log (3 : ℝ)) = 0 := by
      simpa [PhiShape] using hshape3
    rcases mul_eq_zero.mp hmul with hk0 | hsin
    · exact False.elim (hκ hk0)
    · exact hsin

/-- Therefore, Xi has no off-critical zeros. -/
theorem noOffSeed_Xi : NoOffSeed Xi :=
  no_offSeed_of_bridge (hb := stage3Bridge_Xi)

end XiPhaseLock
end Targets
end Hyperlocal
