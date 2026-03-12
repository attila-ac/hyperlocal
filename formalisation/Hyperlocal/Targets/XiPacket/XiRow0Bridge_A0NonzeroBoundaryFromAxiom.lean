/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_A0NonzeroBoundaryFromAxiom.lean

  Legacy compatibility producer for `A0Nonzero`.

  This keeps the historical bridge
      a0_ne_zero_boundary -> A0Nonzero
  available only where explicitly imported.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

instance (s : OffSeed Xi) : A0Nonzero (s := s) :=
  ⟨a0_ne_zero_boundary (s := s)⟩

end XiPacket
end Targets
end Hyperlocal
