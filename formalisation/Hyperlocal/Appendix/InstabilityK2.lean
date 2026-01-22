/-
  Hyperlocal/Appendix/InstabilityK2.lean

  Concrete k=2 instability “toggle”.
  Provides:
    • a trivial instance UnstableHom 2 A t (placeholder),
    • a tiny smoke test showing the abstract bridge closes the contradiction
      as soon as InstabilityK2 is imported.
-/

import Mathlib.Data.Real.Basic
import Hyperlocal.Cancellation.InstabilityHyp

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK2

/-- All real parameters (A,t) yield instability for k=2 (placeholder).
    Replace `⟨trivial⟩` with the genuine characteristic-root argument later. -/
theorem unstable_k2_all_t (A t : ℝ) : UnstableHom 2 A t :=
  ⟨trivial⟩

/-- Typeclass instance form (handy for `haveI` / typeclass search). -/
instance instUnstable_k2 (A t : ℝ) : UnstableHom 2 A t :=
  unstable_k2_all_t A t

/-- **Smoke test**: once the k=2 instance is available, any bridge
    and the Combine “only zero is fine-tuned” fact yield a contradiction. -/
theorem k2_contradiction
    (A t : ℝ)
    (bridge : BridgeData 2 A t)
    (combine_only_zero : ∀ x : Jet6, FineTuned x → x = 0) : False := by
  -- turn on the instance
  haveI : UnstableHom 2 A t := instUnstable_k2 A t
  -- and invoke the abstract hook
  exact no_cancellation_if_unstable bridge combine_only_zero

end InstabilityK2
end Cancellation
end Hyperlocal
