/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalytic.lean

  Analytic landing spot (exports the stable Type-valued name):

    xiJetQuotRow012AtOrder_fromAnalytic : ∀ m s, XiJetQuotRow012AtOrder m s

  Implemented by:
    XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalyticProof.lean

  IMPORTANT:
  This wrapper must remain one-way: it imports the proof file, but the proof file
  must not import this wrapper (otherwise cycles).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalyticProof

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Stable name (Type-valued): downstream should use this `def`. -/
noncomputable def xiJetQuotRow012AtOrder_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_fromAnalyticProof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
