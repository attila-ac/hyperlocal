/-
  Cancellation/BridgeToInstabilityCore.lean
  Minimal helpers: (seed + forces) ↦ BridgeData, and a wrapper to produce `False`.
-/

import Hyperlocal.Cancellation.InstabilityHyp   -- UnstableHom, FineTuned, BridgeData, no_cancellation_if_unstable
import Hyperlocal.Cancellation.Solo             -- Jet6

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace BridgeToInstabilityCore

/-- Package the two hooks into `BridgeData`. -/
def mkBridgeDataFromHooks
    {k : ℕ} {A t : ℝ}
    (seed   : UnstableHom k A t → ∃ x : Jet6, x ≠ 0)
    (forces : ∀ x : Jet6, x ≠ 0 → FineTuned x)
    : BridgeData k A t where
  seed_nontrivial := seed
  forces_fine     := forces

/--
Given hooks `(seed, forces)`, a “combine” lemma that collapses `FineTuned` to `x=0`,
and an instance `[UnstableHom k A t]`, conclude `False`.
-/
theorem contradiction_of_hooks
    {k : ℕ} {A t : ℝ}
    (seed   : UnstableHom k A t → ∃ x : Jet6, x ≠ 0)
    (forces : ∀ x : Jet6, x ≠ 0 → FineTuned x)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0)
    [UnstableHom k A t] :
    False :=
  no_cancellation_if_unstable
    (mkBridgeDataFromHooks seed forces) combine_only_zero

end BridgeToInstabilityCore
end Cancellation
end Hyperlocal
