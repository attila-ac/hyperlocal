import Mathlib.Data.Real.Basic
import Hyperlocal.Cancellation.InstabilityHyp

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1

/-- A named theorem form, if you prefer using a lemma instead of `inferInstance`. -/
theorem unstable_k1_all_t (A t : ℝ) : UnstableHom 1 A t :=
  ⟨trivial⟩

/-- Typeclass instance form (handy for `haveI`/typeclass search). -/
instance instUnstable_k1 (A t : ℝ) : UnstableHom 1 A t :=
  unstable_k1_all_t A t

end InstabilityK1
end Cancellation
end Hyperlocal
