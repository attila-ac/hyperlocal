/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart.lean

  Heart theorem provider (stable API for Frontier/Wrapper).

  IMPORTANT (cycle safety):
  This file MUST NOT import any *default* sigma provider instance derived from frontier,
  because frontier depends (transitively) on heart.
  We only depend on the sigma provider interface, and require the instance as a parameter.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Stable heart output: for any `OffSeed Xi`.

Cycle-safe: consumes sigma via `[XiAtOrderSigmaProvider]` only.
No default instance is imported here.
-/
theorem xiJetQuotRow0AtOrderHeartOut
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    XiJetQuotRow0AtOrderHeartOut m s := by
  classical
  have Hσ : XiAtOrderSigmaOut m s := xiAtOrderSigmaOut_provided (m := m) (s := s)
  exact ⟨Hσ.hw0AtSigma, Hσ.hwp2AtSigma, Hσ.hwp3AtSigma⟩

end XiPacket
end Targets
end Hyperlocal
