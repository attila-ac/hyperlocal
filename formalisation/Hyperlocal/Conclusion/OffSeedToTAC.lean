/-
  Hyperlocal/Conclusion/OffSeedToTAC.lean

  Stage-3 bridge file (SAFE VERSION).

  IMPORTANT FIX:
  The previous version stated the Stage-3 bridge as a global axiom
  for arbitrary H : ℂ → ℂ, which makes the whole development inconsistent
  (e.g. H := 0 has off-seeds).

  This replacement scopes the bridge as an *assumption on a given H*:

      Stage3Bridge H : Prop

  and proves the clean meta-theorem:

      Stage3Bridge H → ¬ Nonempty (OffSeed H)

  So now "Conclusion" is importable and does NOT explode the theory.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.TAC
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Conclusion
namespace OffSeedToTAC

open scoped Real

/-- The exact “TAC trigger” package needed to contradict the two-prime witness. -/
def TAC_trigger (A B : ℝ → ℝ) (κ t : ℝ) : Prop :=
  Hyperlocal.Transport.TAC.EvenF A ∧
  Hyperlocal.Transport.TAC.EvenF B ∧
  Hyperlocal.Cancellation.PrimeWitness.oddPart
      (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 2) t = 0 ∧
  Hyperlocal.Cancellation.PrimeWitness.oddPart
      (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 3) t = 0

/--
Stage-3 bridge *as a property of a particular H*.

This is the single remaining semantic item you must eventually PROVE for ξ:
from an off-critical seed `s : OffSeed H`, produce the TAC trigger data.
-/
structure Stage3Bridge (H : ℂ → ℂ) : Prop :=
  (bridge :
    ∀ s : Hyperlocal.OffSeed H,
      ∃ (A B : ℝ → ℝ) (κ : ℝ), κ ≠ 0 ∧ TAC_trigger A B κ s.ρ.im)

/-- From Stage3Bridge, we contradict the TAC two-prime witness for that seed. -/
theorem offSeed_false_of_bridge
    {H : ℂ → ℂ} (hb : Stage3Bridge H) (s : Hyperlocal.OffSeed H) : False := by
  rcases hb.bridge s with ⟨A, B, κ, hκ, htrig⟩
  rcases htrig with ⟨hA, hB, h2, h3⟩

  have hw :=
    Hyperlocal.Transport.TAC.tac_finite_prime_witness_2_3
      (A := A) (B := B) (κ := κ) (t := s.ρ.im) hA hB hκ s.ht

  cases hw with
  | inl h2ne => exact h2ne h2
  | inr h3ne => exact h3ne h3

/-- Endgame contract for a *fixed* H: there is no off-seed. -/
def NoOffSeed (H : ℂ → ℂ) : Prop :=
  ¬ Nonempty (Hyperlocal.OffSeed H)

/-- Closed contradiction wrapper: Stage3Bridge H implies NoOffSeed H. -/
theorem no_offSeed_of_bridge {H : ℂ → ℂ} (hb : Stage3Bridge H) : NoOffSeed H := by
  intro hne
  rcases hne with ⟨s⟩
  exact offSeed_false_of_bridge (hb := hb) (s := s)

end OffSeedToTAC
end Conclusion
end Hyperlocal
