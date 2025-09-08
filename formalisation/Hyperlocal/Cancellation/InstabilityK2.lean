import Mathlib.Data.Real.Basic
import Hyperlocal.Cancellation.InstabilityHyp

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK2

/-- A named theorem form for k = 2. -/
theorem unstable_k2_all_t (A t : ℝ) : UnstableHom 2 A t :=
  ⟨trivial⟩

/-- Typeclass instance form (useful for `haveI`). -/
instance instUnstable_k2 (A t : ℝ) : UnstableHom 2 A t :=
  unstable_k2_all_t A t

end InstabilityK2
end Cancellation
end Hyperlocal
