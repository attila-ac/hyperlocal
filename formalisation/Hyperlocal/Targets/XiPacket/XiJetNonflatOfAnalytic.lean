/-
  Hyperlocal/Targets/XiPacket/XiJetNonflatOfAnalytic.lean

  Plan C++J semantic endpoint (temporary):

  Provide jet-nonflatness at the critical-line anchor `sc s` in a form usable by
  the jet-pivot window constructor, without any value-level assumption like
  `Re (Xi (sc s)) ≠ 0`.

  Later this should be discharged from analyticity + `Xi` not identically zero
  (identity theorem / nonflatness).
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Semantic endpoint (temporary): some jet has nonzero real part at `sc s`. -/
axiom xiJetNonflat_re_exists (s : OffSeed Xi) :
    ∃ m : ℕ, ((cderivIter m Xi) (sc s)).re ≠ 0

end XiPacket
end Targets
end Hyperlocal
