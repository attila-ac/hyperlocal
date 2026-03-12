/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0WitnessAtOrderFromRow012Upstream.lean

  Legacy compatibility surface for the row-0 witness at order.

  IMPORTANT:
  * keep this file on the ambient compatibility corridor for now
  * do NOT retarget it through the theorem-side true-analytic gate here
  * this file exists to keep the repo buildable while the theorem cone is being moved
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

noncomputable def xiJetQuotRow0WitnessCAtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  simpa using xiJetQuotRow0WitnessCAtOrder (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
