/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_TwoPrimeNondegeneracy_FromToeplitzGuardrails.lean
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Gate_FromTwoPrimeNondegeneracy
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2Data_WireFromToeplitz
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2ConnectorDeterministic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLImpossibility

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

namespace W1

instance instXiPrimeWitnessW1TwoPrimeNondegeneracy_fromGuardrails
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiPrimeWitnessW1TwoPrimeNondegeneracy
      (m := m) (s := s)
      (tval := ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ)) :=
by
  classical
  refine ⟨?_⟩
  intro htv

  by_contra hOr
  push_neg at hOr
  rcases hOr with ⟨h2, h3⟩

  rcases
      (toeplitzL_wc_of_Fwp2_Fwp3_zero (m := m) (s := s) h2 h3 htv)
    with ⟨c, hc, hToe⟩

  exact
    (ToeplitzGuardrails.no_nonzero_toeplitzL_annihilator_for_wc (s := s))
      ⟨c, hc, hToe⟩

end W1

end XiPacket
end Targets
end Hyperlocal
