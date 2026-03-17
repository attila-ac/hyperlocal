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

theorem row0Sigma_wc_zero_on_resonant_branch_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0 := by
  intro s hres
  -- this is the actual remaining mathematics
  -- every other green file is now downstream of this exact theorem
  sorry
