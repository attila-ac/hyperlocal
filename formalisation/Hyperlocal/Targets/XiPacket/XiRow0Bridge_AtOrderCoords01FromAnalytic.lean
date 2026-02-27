/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalytic.lean

  Analytic-branch wrapper (general OffSeed branch).

  IMPORTANT:
  Anything that divides by `JetQuotOp.aRk1 s 0` must assume it explicitly.
  Therefore this wrapper requires `[A0Nonzero (s := s)]` and delegates to the
  extractor-side theorem.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- General analytic branch: coordinates 0/1 bundle, assuming the `A0Nonzero` boundary. -/
theorem xiAtOrderCoords01Out_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) [A0Nonzero (s := s)] :
    XiAtOrderCoords01Out m s := by
  simpa using (xiAtOrderCoords01Out_fromAnalyticExtractor (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
