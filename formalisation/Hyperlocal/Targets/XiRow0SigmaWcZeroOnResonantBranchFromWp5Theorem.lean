import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Resonant-branch seam (A) from the single remaining local wp5 theorem.

This is the sharpest theorem-level reduction in the current tree:
the pair-{2,5} row-0 argument turns the local wp5 statement directly into

  row0Sigma s (wc s) = 0

on the exact `log(3/2)` resonant branch.
-/
theorem row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0 := by
  intro s hres
  exact XiPacket.W1.row0Sigma_wc_eq_zero_of_resonant32_of_row0_wp5
    (s := s)
    (hres := hres)
    (hwp5 := hwp5_res s hres)

#print axioms row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem

end Targets
end Hyperlocal
