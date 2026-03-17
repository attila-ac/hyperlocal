import Hyperlocal.Targets.XiPair25ResonantScalarProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Installed bundled pair-{2,5} resonant scalar provider from the two explicit
theorem inputs.

This packages the last two ordinary theorem arguments
  * σ2 = 2 * delta on the resonant branch
  * bCoeff(...,5) = 0 on the resonant branch
into a single stable provider surface.
-/
instance instXiPair25ResonantScalarProviderInstalled
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    XiPair25ResonantScalarProvider where
  sigma2_eq_two_delta_on_resonant_branch_global := hσ2δ_res
  bCoeff5_zero_on_resonant_branch_global := hb5_res

end Targets
end Hyperlocal
