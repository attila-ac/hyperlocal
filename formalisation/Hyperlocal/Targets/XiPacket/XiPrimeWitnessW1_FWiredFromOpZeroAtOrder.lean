/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_FWiredFromOpZeroAtOrder.lean

  Bridge file (purely deterministic):

    XiJetQuotOpZeroAtOrder m s
      ⇒  FWired m s (w0At m s)  = 0
      ⇒  FWired m s (wp2At m s) = 0
      ⇒  FWired m s (wp3At m s) = 0

  No analytic content.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Gate_FromTwoPrimeNondegeneracy
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2Data_WireFromToeplitz

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

open Hyperlocal.Transport

section

variable (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi)

/-- Unfold `FWired` to the installed `XiPrimeWitnessW1Defs.F` from Toeplitz wiring. -/
@[simp] lemma FWired_def :
    FWired (m := m) (s := s)
      =
    (by
      classical
      letI := instXiPrimeWitnessW1Defs_xi_fromToeplitz (m := m) (s := s)
      exact (XiPrimeWitnessW1Defs.F
        (R := ℂ) (V := Window 3) (W := Window 3) (H := W1.Xi) (s := s))) := by
  classical
  rfl

/-- `hop_w0At` → `FWired w0At = 0`. -/
theorem FWired_w0At_eq_zero
    (hOp : XiJetQuotOpZeroAtOrder m s) :
    FWired (m := m) (s := s) (w0At m s) = 0 := by
  classical
  -- unfold FWired; the target becomes exactly the `hop_w0At` field
  simpa [FWired, FWired_def (m := m) (s := s)] using hOp.hop_w0At

/-- `hop_wp2At` → `FWired wp2At = 0`. -/
theorem FWired_wp2At_eq_zero
    (hOp : XiJetQuotOpZeroAtOrder m s) :
    FWired (m := m) (s := s) (wp2At m s) = 0 := by
  classical
  simpa [FWired, FWired_def (m := m) (s := s)] using hOp.hop_wp2At

/-- `hop_wp3At` → `FWired wp3At = 0`. -/
theorem FWired_wp3At_eq_zero
    (hOp : XiJetQuotOpZeroAtOrder m s) :
    FWired (m := m) (s := s) (wp3At m s) = 0 := by
  classical
  simpa [FWired, FWired_def (m := m) (s := s)] using hOp.hop_wp3At

end

end W1
end XiPacket
end Targets
end Hyperlocal
