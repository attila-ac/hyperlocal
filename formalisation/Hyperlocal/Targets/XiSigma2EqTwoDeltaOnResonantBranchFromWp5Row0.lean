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
Pair-{2,5} local reduction on the exact log(3/2)-resonant branch:

if the remaining local row-0 theorem at `wpAt 0 s 5` is available, then the
preferred seam `(A)` already closes:
  row0Sigma s (wc s) = 0.
-/
theorem row0Sigma_wc_zero_on_resonant_branch_of_wp5_row0
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hwp5 :
      row0Sigma s (wpAt 0 s 5) = 0) :
    row0Sigma s (wc s) = 0 := by
  exact W1.row0Sigma_wc_eq_zero_of_resonant32_of_row0_wp5
    (s := s) (hres := hres) (hwp5 := hwp5)

/--
Packaged branch-local version of the previous theorem.

So once you prove the single local theorem

  ∀ s, sin(t(s) log(3/2)) = 0 -> row0Sigma s (wpAt 0 s 5) = 0

you immediately get the branch-local seam `(A)` package.
-/
theorem row0Sigma_wc_zero_on_resonant_branch_all_of_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0 := by
  intro s hres
  exact row0Sigma_wc_zero_on_resonant_branch_of_wp5_row0
    (s := s) (hres := hres) (hwp5 := hwp5_res s hres)

/--
Same pair-{2,5} local reduction, now pushed one step further to equivalent form `(C)`:

from the local `wpAt 0 s 5` row-0 theorem on the resonant branch,
derive the scalar midpoint
  σ2 = 2 * delta.
-/
theorem sigma2_eq_two_delta_on_resonant_branch_of_wp5_row0
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0)
    (hwp5 :
      row0Sigma s (wpAt 0 s 5) = 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  have hsigma : row0Sigma s (wc s) = 0 := by
    exact row0Sigma_wc_zero_on_resonant_branch_of_wp5_row0
      (s := s) (hres := hres) (hwp5 := hwp5)

  have hclosed :
      row0Sigma s (wc s)
        =
      (JetQuotOp.σ2 s : ℂ) - (2 : ℂ) * (XiTransport.delta s : ℂ) := by
    simpa using (W1.row0Sigma_wc_closed (s := s))

  rw [hsigma] at hclosed
  have hz :
      (JetQuotOp.σ2 s : ℂ) - (2 : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    simpa using hclosed.symm

  exact sub_eq_zero.mp hz

/--
Packaged branch-local version of the previous theorem.

This is the honest replacement target for the old `sorry`-bearing attempt:
the scalar midpoint now follows from the strictly smaller local theorem at `wpAt 0 s 5`.
-/
theorem sigma2_eq_two_delta_on_resonant_branch_all_of_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  intro s hres
  exact sigma2_eq_two_delta_on_resonant_branch_of_wp5_row0
    (s := s) (hres := hres) (hwp5 := hwp5_res s hres)

end Targets
end Hyperlocal
