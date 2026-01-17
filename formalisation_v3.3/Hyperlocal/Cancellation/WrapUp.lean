/-
  Hyperlocal/Cancellation/WrapUp.lean

  Final wrappers that close the contradiction once:
    • the abstract bridge `BridgeData k A t` is provided, and
    • the Combine fact “only zero is fine-tuned” holds at (A₀, t₀).

  We provide k=1 and k=2 flavors that turn on the corresponding
  UnstableHom instances (currently placeholders) and apply the abstract hook.
-/

import Mathlib.Data.Real.Basic
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.InstabilityK1
import Hyperlocal.Cancellation.InstabilityK2

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace WrapUp

/-- Final wrapper (k=1): with a bridge and the Combine-only-zero fact,
    instability at k=1 yields a contradiction. -/
theorem no_off_critical_zero_k1
    (A t : ℝ)
    (bridge : BridgeData 1 A t)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0) : False := by
  -- enable the k=1 instability instance
  haveI : UnstableHom 1 A t := InstabilityK1.instUnstable_k1 A t
  -- abstract hook closes the contradiction
  exact no_cancellation_if_unstable bridge combine_only_zero

/-- Final wrapper (k=2): with a bridge and the Combine-only-zero fact,
    instability at k=2 yields a contradiction. -/
theorem no_off_critical_zero_k2
    (A t : ℝ)
    (bridge : BridgeData 2 A t)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0) : False := by
  -- enable the k=2 instability instance
  haveI : UnstableHom 2 A t := InstabilityK2.instUnstable_k2 A t
  -- abstract hook closes the contradiction
  exact no_cancellation_if_unstable bridge combine_only_zero

end WrapUp
end Cancellation
end Hyperlocal
