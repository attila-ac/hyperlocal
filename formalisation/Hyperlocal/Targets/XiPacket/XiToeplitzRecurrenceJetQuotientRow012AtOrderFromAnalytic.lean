/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalytic.lean

  Analytic landing spot (exports the stable Type-valued name):

    xiJetQuotRow012AtOrder_fromAnalytic : ∀ m s, XiJetQuotRow012AtOrder m s

  Implemented by:
    ...Row012AtOrderFromAnalyticProof.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalyticProof

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Stable name (Type-valued): downstream should use this `def`. -/
noncomputable def xiJetQuotRow012AtOrder_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_fromAnalytic_proof (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
