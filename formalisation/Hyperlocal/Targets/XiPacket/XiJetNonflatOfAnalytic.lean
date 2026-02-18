import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiWindowScNonvanishing
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-- Semantic endpoint: there exists some jet coordinate with nonzero real part. -/
theorem xiJetNonflat_re_exists (s : Hyperlocal.OffSeed Xi) :
  ∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0 := by
  -- Discharge using the anchor nonvanishing at `m = 0`.
  refine ⟨0, ?_⟩
  -- `cderivIter 0 Xi = Xi`.
  simpa [cderivIter] using (xi_sc_re_ne_zero (s := s))

end XiPacket
end Targets
end Hyperlocal
