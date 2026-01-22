-- Hyperlocal/Appendix/InstabilityK1_Mid.lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Appendix.InstabilityK1_Fillers

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1
namespace Mid

def t1_mid : ℝ := 1/10
def t2_mid : ℝ := 10

/-- Mid-range instability (stub). Replace body by UC/Schur–Cohn proof later. -/
theorem unstable_mid (A : ℝ) :
  ∀ {t : ℝ}, t1_mid ≤ t → t ≤ t2_mid → UnstableHom 1 A t := by
  intro t _ _
  exact ⟨trivial⟩

/-- Packaged mid-range hypothesis for the aggregator. -/
def MidHyp_pkg (A : ℝ) : MidHyp A t1_mid t2_mid :=
{ h12 := by
    have h : (1/10 : ℝ) ≤ 10 := by norm_num
    simpa [t1_mid, t2_mid] using h,
  prove := by
    intro t ht1 ht2; exact unstable_mid A ht1 ht2 }

end Mid
end InstabilityK1
end Cancellation
end Hyperlocal
