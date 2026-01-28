/-
  Hyperlocal/Conclusion/OffSeedToTAC.lean

  Stage-3 bridge file (repo-API correct).

  Goal: isolate the *single* semantic-debt item as one axiom:

    OffSeed → ∃ A B κ, κ ≠ 0 ∧ (EvenF A) ∧ (EvenF B)
              ∧ oddPart (PhiPrime A B (fun _ => κ) 2) t = 0
              ∧ oddPart (PhiPrime A B (fun _ => κ) 3) t = 0

  This is exactly what `Hyperlocal/Transport/TAC.lean` needs to fire
  the two-prime witness contradiction.

  Everything else is definitional glue and a closed contradiction proof.
-/

import Hyperlocal.Transport.TAC
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Conclusion
namespace OffSeedToTAC

open scoped Real

/-- Minimal “off-seed” carrier for the Stage-3 bridge layer.

You can later replace/alias this with your upstream off-critical seed object;
for the bridge itself we only need `(k,A,t)` and `t ≠ 0`.
-/
structure OffSeed where
  k : ℕ
  A : ℝ
  t : ℝ
  ht : t ≠ 0

/-- The exact “TAC trigger” package needed to contradict the two-prime witness. -/
def TAC_trigger (A B : ℝ → ℝ) (κ t : ℝ) : Prop :=
  Hyperlocal.Transport.TAC.EvenF A ∧
  Hyperlocal.Transport.TAC.EvenF B ∧
  Hyperlocal.Cancellation.PrimeWitness.oddPart
      (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 2) t = 0 ∧
  Hyperlocal.Cancellation.PrimeWitness.oddPart
      (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 3) t = 0

/-
  ===========================
  Stage-3 semantic debt item:
  ===========================

  Once this is proved from your analytic transport layer,
  the downstream two-prime witness closes the contradiction with no further axioms.
-/
axiom offSeed_to_TAC_trigger (s : OffSeed) :
  ∃ (A B : ℝ → ℝ) (κ : ℝ), κ ≠ 0 ∧ TAC_trigger A B κ s.t

/-- From the bridge axiom, we immediately contradict the TAC two-prime witness. -/
theorem offSeed_false (s : OffSeed) : False := by
  rcases offSeed_to_TAC_trigger s with ⟨A, B, κ, hκ, htrig⟩
  have hA : Hyperlocal.Transport.TAC.EvenF A := htrig.1
  have hB : Hyperlocal.Transport.TAC.EvenF B := htrig.2.1
  have h2 :
      Hyperlocal.Cancellation.PrimeWitness.oddPart
        (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 2) s.t = 0 :=
    htrig.2.2.1
  have h3 :
      Hyperlocal.Cancellation.PrimeWitness.oddPart
        (Hyperlocal.Transport.TAC.PhiPrime A B (fun _ => κ) 3) s.t = 0 :=
    htrig.2.2.2

  have hw :=
    Hyperlocal.Transport.TAC.tac_finite_prime_witness_2_3
      (A := A) (B := B) (κ := κ) (t := s.t) hA hB hκ s.ht

  -- `hw` is an OR of non-vanishing; kill each branch using the corresponding `= 0`.
  cases hw with
  | inl h2ne => exact h2ne h2
  | inr h3ne => exact h3ne h3

/-- Convenience: no off-seed exists (relative only to the single bridge axiom). -/
theorem no_offSeed : ¬ (∃ s : OffSeed, True) := by
  rintro ⟨s, _⟩
  exact offSeed_false s

end OffSeedToTAC
end Conclusion
end Hyperlocal
