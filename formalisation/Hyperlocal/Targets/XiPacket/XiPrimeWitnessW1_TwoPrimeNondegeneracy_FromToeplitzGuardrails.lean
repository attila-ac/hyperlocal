/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_TwoPrimeNondegeneracy_FromToeplitzGuardrails.lean

  Install:
    instance : XiPrimeWitnessW1TwoPrimeNondegeneracy (m := m) (s := s) (tval := ...)

  using the Toeplitz guardrail:
    ToeplitzGuardrails.no_nonzero_toeplitzL_annihilator_for_wc

  Remaining dependency:
    a single bridge lemma that produces a nonzero `c : Fin 3 → ℝ`
    and an annihilation statement
      toeplitzL 2 (coeffsNat3 c) (wc s) = 0
    from the hypothesis
      W1.FWired m s (wp2At m s) = 0 ∧ W1.FWired m s (wp3At m s) = 0.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Gate_FromTwoPrimeNondegeneracy
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLImpossibility

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

open Hyperlocal.Transport
open Hyperlocal.Targets.XiPacket  -- for `wc`, `wp2At`, `wp3At`
open scoped BigOperators

section

variable (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi)

/-- The scalar used for the `tval` parameter in the gate-class. -/
abbrev tval (s : Hyperlocal.OffSeed W1.Xi) : ℂ :=
  (Hyperlocal.Targets.XiTransport.delta s : ℂ)

/-
Connector still missing (replace this axiom by the real lemma you locate):

From
  W1.FWired m s (wp2At m s) = 0 and W1.FWired m s (wp3At m s) = 0
produce a nonzero c : Fin 3 → ℝ with
  toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (wc s) = 0.
-/
axiom toeplitzL_wc_annihilation_of_Fwp2_Fwp3_zero
    (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi)
    (h2 : W1.FWired (m := m) (s := s) (wp2At m s) = 0)
    (h3 : W1.FWired (m := m) (s := s) (wp3At m s) = 0) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧
      (Hyperlocal.Transport.toeplitzL 2
        (Hyperlocal.Targets.XiPacket.ToeplitzLToRow3.coeffsNat3 c)
        (Hyperlocal.Targets.XiPacket.wc s)) = 0

/-- Adapter: Toeplitz guardrail ⇒ two-prime nondegeneracy (for `tval := delta s`). -/
instance instXiPrimeWitnessW1TwoPrimeNondegeneracy_fromGuardrails :
    XiPrimeWitnessW1TwoPrimeNondegeneracy (m := m) (s := s) (tval := tval s) :=
by
  classical
  refine ⟨?_⟩
  intro ht
  -- prove disjunction by contradiction
  by_contra h
  -- h : ¬(FWired(wp2)≠0 ∨ FWired(wp3)≠0)

  have h2 :
      W1.FWired (m := m) (s := s) (wp2At m s) = 0 := by
    by_contra hne
    exact h (Or.inl hne)

  have h3 :
      W1.FWired (m := m) (s := s) (wp3At m s) = 0 := by
    by_contra hne
    exact h (Or.inr hne)

  rcases toeplitzL_wc_annihilation_of_Fwp2_Fwp3_zero (m := m) (s := s) h2 h3 with
    ⟨c, hcne, hT⟩

  -- Contradict the guardrail: off-critical seeds admit no nonzero annihilator for `wc`.
  have : False :=
    (Hyperlocal.Targets.XiPacket.ToeplitzGuardrails.no_nonzero_toeplitzL_annihilator_for_wc (s := s)).elim
      ⟨c, hcne, hT⟩

  exact this

end

end W1
end XiPacket
end Targets
end Hyperlocal
