/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_TwoPrimeNondegeneracy_FromToeplitzGuardrails.lean

  Frontier (compiling stub version):

  Goal shape (axiom-free *design*):
    FWired(wp2At) ≠ 0 ∨ FWired(wp3At) ≠ 0
  by contradiction using Toeplitz guardrail:
    no_nonzero_toeplitzL_annihilator_for_wc

  STATUS:
  - This file **compiles** and cleanly marks the single missing deterministic connector
    as a local theorem stub (with `sorry`).
  - Once you discharge that connector in the Stage-2 wiring layer, delete the `sorry`
    here and replace by `exact <your lemma>`.

  IMPORTANT:
  - We DO NOT attempt the bogus operator rewrite (aRk1 s vs coeffsNat3 c).
    That is exactly the mismatch error you saw.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Gate_FromTwoPrimeNondegeneracy
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2Data_WireFromToeplitz
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLImpossibility
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientEllFromOperator

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

namespace W1

/-
  SINGLE FRONTIER LEMMA (the only missing deterministic bridge):

  From the two FWired-zeros at wp2At/wp3At, build a nonzero real stencil `c`
  such that the ToeplitzL operator built from `coeffsNat3 c` annihilates `wc s`.

  This is exactly what your earlier draft tried to manufacture by rewriting coords,
  but that approach forced the impossible identification:
    aRk1 s  =  coeffsNat3 c.

  Instead, prove this in the Stage-2 wiring layer using your existing
  Toeplitz/shift/transport algebra, and keep this guardrails consumer file tiny.
-/
private theorem toeplitzL_wc_of_Fwp2_Fwp3_zero
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (h2 : FWired (m := m) (s := s) (wp2At m s) = 0)
    (h3 : FWired (m := m) (s := s) (wp3At m s) = 0) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧
      toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (wc s) = 0 := by
  classical
  -- FRONTIER STUB:
  -- Replace this `sorry` by the actual deterministic proof once you finish the
  -- Stage-2 wiring connector.
  sorry

/-- Guardrails instance: Toeplitz impossibility forces two-prime nondegeneracy. -/
instance instXiPrimeWitnessW1TwoPrimeNondegeneracy_fromGuardrails
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiPrimeWitnessW1TwoPrimeNondegeneracy
      (m := m) (s := s)
      (tval := Hyperlocal.Targets.XiTransport.delta s) :=
by
  classical
  refine ⟨?nondeg⟩
  intro _ht
  by_contra hOr
  push_neg at hOr
  rcases hOr with ⟨h2, h3⟩

  rcases toeplitzL_wc_of_Fwp2_Fwp3_zero (m := m) (s := s) h2 h3 with
    ⟨c, hc_ne, hToe⟩

  exact
    (Hyperlocal.Targets.XiPacket.ToeplitzGuardrails.no_nonzero_toeplitzL_annihilator_for_wc (s := s))
      ⟨c, hc_ne, hToe⟩

end W1

end XiPacket
end Targets
end Hyperlocal
