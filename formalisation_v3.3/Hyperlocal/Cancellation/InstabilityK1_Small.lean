-- Hyperlocal/Cancellation/InstabilityK1_Small.lean
import Mathlib.Data.Real.Basic
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.InstabilityK1_Fillers

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1
namespace Small

/-- (placeholder) any 1 < R < |1/A| later; pick anything now -/
def R_small (A : ℝ) : ℝ := (3 : ℝ) / 2

/-- (placeholder) perturbation bound constant; wire real bound later -/
def C_small (A : ℝ) : ℝ := 1

/-- (placeholder) small threshold; pick a clean positive number -/
def t1_small (A : ℝ) : ℝ := 1

/-- Small-t instability (stub). Replace body by the Rouché proof later. -/
theorem unstable_small
  (A : ℝ) :
  ∀ {t : ℝ}, 0 < t → t ≤ t1_small A → UnstableHom 1 A t := by
  intro t _ _
  exact ⟨trivial⟩

/-- Packaged small-t hypothesis for the aggregator. -/
def SmallHyp_pkg (A : ℝ) : SmallHyp A (t1_small A) :=
{ h0 := by
    -- 0 < 1
    simpa [t1_small] using (zero_lt_one : (0 : ℝ) < 1),
  prove := by
    intro t ht htle; exact unstable_small A ht htle }

end Small
end InstabilityK1
end Cancellation
end Hyperlocal
