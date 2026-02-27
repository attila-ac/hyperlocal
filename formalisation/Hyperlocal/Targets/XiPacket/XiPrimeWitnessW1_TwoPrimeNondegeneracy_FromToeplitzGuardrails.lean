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
      (tval := Complex.ofReal (Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))))) :=
by
  classical
  refine ⟨by
    intro htv

    -- Convert `tval ≠ 0` (in ℂ) into the real sine nonzero hypothesis.
    have hsin :
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) ≠ 0 := by
      intro h0
      apply htv
      -- (h0 : sin(...) = 0) ⇒ Complex.ofReal (sin(...)) = 0
      simpa [h0]

    -- Provide the missing implicit `{ht : XiTransport.delta s ≠ 0}` from OffSeed.
    have ht : Hyperlocal.Targets.XiTransport.delta s ≠ 0 := by
      -- delta s = s.ρ.re - 1/2, and OffSeed has `s.hσ : s.ρ.re ≠ 1/2`
      simpa [Hyperlocal.Targets.XiTransport.delta] using (sub_ne_zero.mpr s.hσ)

    -- If both wired outputs were zero, Stage-2 would manufacture a nonzero Toeplitz annihilator for wc,
    -- contradicting guardrails.
    by_contra hOr
    push_neg at hOr
    rcases hOr with ⟨h2, h3⟩

    rcases
        (toeplitzL_wc_of_Fwp2_Fwp3_zero (m := m) (s := s) (ht := ht) h2 h3 hsin)
      with ⟨c, hc, hToe⟩

    exact
      (ToeplitzGuardrails.no_nonzero_toeplitzL_annihilator_for_wc (s := s))
        ⟨c, hc, hToe⟩
  ⟩

end W1

end XiPacket
end Targets
end Hyperlocal
