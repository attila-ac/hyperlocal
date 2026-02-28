/-
  Hyperlocal/Targets/XiPacket/XiRouteA_NonflatLe2.lean

  Task D (Plan C++J): bounded nonflatness statement for Route–A witness `routeA_G s`.

  We deliberately avoid Mathlib's IteratedDeriv (missing in your snapshot).
  We use the project’s snapshot-robust iterator `cderivIter` (already present in
  XiWindowJetPivotDefs / your jet plumbing).

  Statement:
    ∀ s z, ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) z ≠ 0
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs  -- provides `cderivIter`
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Bounded nonflatness (≤2) of the Route–A witness at an arbitrary anchor `z`. -/
axiom routeA_G_nonflat_le2 (s : OffSeed Xi) (z : ℂ) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) z ≠ 0

end XiPacket
end Targets
end Hyperlocal
