import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization

/--
BRIDGE LEMMA (The real missing link):
Relates the algebraic Toeplitz row sum to the analytic polynomial evaluation.
-/
lemma row0Sigma_eq_eval (s : OffSeed Xi) (w : Fin 3 → ℂ) (z : ℂ) :
row0Sigma s w = (Rquartet s.ρ).eval z := by
admit

/-- Route-A: analytic discharge of the row-0 scalar goals. -/
noncomputable def xiJetQuot_row0_scalarGoals_analytic (s : Hyperlocal.OffSeed Xi) :
XiJetQuotRow0ScalarGoals s where
hw0 := by {
rw [row0Sigma_eq_eval s (w0 s) s.ρ]
exact (R_quartet_zeros s).1
}
hwc := by {
rw [row0Sigma_eq_eval s (wc s) (1 - s.ρ)]
exact (R_quartet_zeros s).2.2.1
}
hwp2 := by {
rw [row0Sigma_eq_eval s (wp2 s) (star s.ρ)]
exact (R_quartet_zeros s).2.1
}
hwp3 := by {
rw [row0Sigma_eq_eval s (wp3 s) (1 - star s.ρ)]
exact (R_quartet_zeros s).2.2.2
}

/-- Public stable name. -/
noncomputable def xiJetQuot_row0_scalarGoals (s : Hyperlocal.OffSeed Xi) :
XiJetQuotRow0ScalarGoals s :=
xiJetQuot_row0_scalarGoals_analytic s

end XiPacket
end Targets
end Hyperlocal
