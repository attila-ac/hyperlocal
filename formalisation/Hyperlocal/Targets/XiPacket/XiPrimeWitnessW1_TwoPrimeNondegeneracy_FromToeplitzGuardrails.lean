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
      (tval := Hyperlocal.Targets.XiTransport.delta s) :=
by
  classical
  refine ⟨?_⟩
  intro htv

  -- Convert htv : (↑(delta s)) ≠ 0 into ht : (delta s) ≠ 0.
  -- This is the only real issue in this file.
  have ht : Hyperlocal.Targets.XiTransport.delta s ≠ 0 := by
    -- Most coercions support this:
    -- (If this fails in your snapshot, replace `exact_mod_cast` by the `simpa` line below.)
    first
      | exact_mod_cast htv
      | -- fallback: try to push the coercion back by simp/norm_cast
        -- This works if the coercion is `Subtype.val`-like or a ring coercion simp can see.
        -- In many cases `simp` alone reduces `((↑x : α) = 0)` to `(x = 0)`.
        -- We use contrapositive style.
        intro hx
        apply htv
        simpa [hx]

  by_contra hOr
  push_neg at hOr
  rcases hOr with ⟨h2, h3⟩

  rcases
      (toeplitzL_wc_of_Fwp2_Fwp3_zero (m := m) (s := s) (ht := ht) h2 h3)
    with ⟨c, hc, hToe⟩

  exact
    (ToeplitzGuardrails.no_nonzero_toeplitzL_annihilator_for_wc (s := s))
      ⟨c, hc, hToe⟩

end W1

end XiPacket
end Targets
end Hyperlocal
