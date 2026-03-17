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
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
On the exact `log(3/2)` resonant branch, the local wp5 row-0 theorem already
forces the pair-{2,5} scalar tail coefficient to vanish:

  bCoeff (σ s) (t s) 5 = 0.

So after wp5 is available, the split pair-{2,5} scalar surface has no
independent `bCoeff5` burden left.
-/
theorem bCoeff5_zero_on_resonant_branch_of_wp5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      bCoeff (σ s) (t s) (5 : ℝ) = 0 := by
  intro s hres

  have hsigma : row0Sigma s (wc s) = 0 := by
    exact Hyperlocal.Targets.XiPacket.W1.row0Sigma_wc_eq_zero_of_resonant32_of_row0_wp5
      (s := s)
      (hres := hres)
      (hwp5 := hwp5_res s hres)

  have hcf := Hyperlocal.Targets.XiPacket.W1.row0Sigma_wpAt5_closed_form (s := s)

  have htmp : (0 : ℂ) = -((2 : ℂ) * (bCoeff (σ s) (t s) (5 : ℝ) : ℂ)) := by
    rw [hwp5_res s hres, hsigma] at hcf
    simpa [sub_eq_add_neg] using hcf

  have hz : ((2 : ℂ) * (bCoeff (σ s) (t s) (5 : ℝ) : ℂ)) = 0 := by
    have hneg := congrArg Neg.neg htmp
    simpa using hneg

  have h2 : (2 : ℂ) ≠ 0 := by
    norm_num

  exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h2)

#print axioms bCoeff5_zero_on_resonant_branch_of_wp5

end Targets
end Hyperlocal
