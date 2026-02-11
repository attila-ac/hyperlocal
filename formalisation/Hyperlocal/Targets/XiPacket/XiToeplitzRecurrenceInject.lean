/-
Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceInject.lean

Replace axioms by theorems (now safe: Identity no longer imports Semantics/Inject).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentity

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real BigOperators
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket  -- <-- brings `bCoeff` into scope

theorem xiToeplitz_hb2_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  have hp : (2 : ℝ) = (2 : ℝ) ∨ (2 : ℝ) = (3 : ℝ) := Or.inl rfl
  simpa using (xiToeplitzRecurrenceIdentity_p (s := s) (p := (2 : ℝ)) hp)

theorem xiToeplitz_hb3_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  have hp : (3 : ℝ) = (2 : ℝ) ∨ (3 : ℝ) = (3 : ℝ) := Or.inr rfl
  simpa using (xiToeplitzRecurrenceIdentity_p (s := s) (p := (3 : ℝ)) hp)

end XiPacket
end Targets
end Hyperlocal
