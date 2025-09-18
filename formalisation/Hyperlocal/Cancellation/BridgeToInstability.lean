-- Cancellation/BridgeToInstability.lean
/-
  Glue layer: package the two “hooks” (seed & forces) into BridgeData,
  and expose a one-liner wrapper to get the contradiction once an
  UnstableHom instance is available.
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Cancellation.Solo          -- Jet6
import Hyperlocal.Cancellation.Setup         -- A₀, t₀
import Hyperlocal.Cancellation.QCC           -- QCCfun
import Hyperlocal.Cancellation.TRC           -- TRCfun
import Hyperlocal.Cancellation.InstabilityHyp

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace BridgeToInstability

/-- Re-expose the FineTuned predicate so callers see the whole picture here. -/
open Hyperlocal.Cancellation (FineTuned UnstableHom BridgeData no_cancellation_if_unstable)

/--
Constructor: build `BridgeData k A t` from two **hooks** you’ll prove elsewhere:

* `seed`   : under instability, produce a nonzero jet,
* `forces` : any such nonzero jet must satisfy `FineTuned` at (A₀,t₀).

This avoids trying to *construct* a nonzero jet here (which caused the `decide` error),
and keeps this file pure scaffolding.
-/
def mkBridgeDataFromHooks
    {k : ℕ} {A t : ℝ}
    (seed   : UnstableHom k A t → ∃ x : Jet6, x ≠ 0)
    (forces : ∀ x : Jet6, x ≠ 0 → FineTuned x) :
    BridgeData k A t where
  seed_nontrivial := seed
  forces_fine     := forces

/--
One-line wrapper: if you give the two hooks above *and* the Combine lemma
(`FineTuned x → x = 0`), then any instance `[UnstableHom k A t]` yields `False`.
-/
theorem contradiction_of_hooks
    {k : ℕ} {A t : ℝ}
    (seed   : UnstableHom k A t → ∃ x : Jet6, x ≠ 0)
    (forces : ∀ x : Jet6, x ≠ 0 → FineTuned x)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0)
    [UnstableHom k A t] :
    False :=
  no_cancellation_if_unstable
    (mkBridgeDataFromHooks seed forces)
    combine_only_zero

end BridgeToInstability
end Cancellation
end Hyperlocal
