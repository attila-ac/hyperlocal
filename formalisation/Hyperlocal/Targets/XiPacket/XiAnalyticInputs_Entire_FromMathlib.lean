import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Basic
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.GrowthOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.GrowthOrder

private abbrev Xi : ℂ → ℂ := Hyperlocal.xi

theorem completedRiemannZeta_analyticAt (z : ℂ) :
    AnalyticAt ℂ completedRiemannZeta z := by
  classical
  sorry

theorem Xi_entire : EntireFun Xi := by
  intro z

  -- IMPORTANT: force the goal into the unfolded form of `xi`
  -- (this is exactly what your FE proof saw)
  change AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ)) * completedRiemannZeta w) z

  have h_id  : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have h_one : AnalyticAt ℂ (fun _w : ℂ => (1 : ℂ)) z := analyticAt_const
  have h_sub : AnalyticAt ℂ (fun w : ℂ => w - (1 : ℂ)) z := h_id.sub h_one
  have h_poly : AnalyticAt ℂ (fun w : ℂ => w * (w - (1 : ℂ))) z := h_id.mul h_sub
  have h_zeta : AnalyticAt ℂ completedRiemannZeta z :=
    completedRiemannZeta_analyticAt (z := z)

  -- product, then reassociate
  have h_prod :
      AnalyticAt ℂ (fun w : ℂ => (w * (w - (1 : ℂ))) * completedRiemannZeta w) z :=
    h_poly.mul h_zeta

  simpa [mul_assoc] using h_prod

end XiPacket
end Targets
end Hyperlocal
