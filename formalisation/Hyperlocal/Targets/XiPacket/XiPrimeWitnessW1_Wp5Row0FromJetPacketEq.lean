import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiWindowJetPivot_wpAtExpand
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real

namespace W1

/--
If a generic prime window actually coincides with the transported central window `w0At`,
then its row-0 sigma vanishes immediately.

This is the clean “jet packet equality ⇒ row-0 zero” bridge.
-/
theorem row0Sigma_wpAt_eq_zero_of_eq_w0At
    (m : ℕ)
    (s : Hyperlocal.OffSeed Xi)
    (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hEq : wpAt m s p = w0At m s) :
    row0Sigma s (wpAt m s p) = 0 := by
  rw [hEq]
  exact sigma_w0At (m := m) (s := s)

/--
Specialised `p = 5`, `m = 0` version used by the final resonant-branch corridor.
-/
theorem row0Sigma_wpAt5_eq_zero_of_eq_w0At
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hEq : wpAt 0 s 5 = w0At 0 s) :
    row0Sigma s (wpAt 0 s 5) = 0 := by
  exact row0Sigma_wpAt_eq_zero_of_eq_w0At
    (m := 0) (s := s) (p := 5) (hEq := hEq)

end W1

end XiPacket
end Targets
end Hyperlocal
