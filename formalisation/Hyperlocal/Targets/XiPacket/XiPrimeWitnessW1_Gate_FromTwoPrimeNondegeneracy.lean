/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Gate_FromTwoPrimeNondegeneracy.lean

  W1 analytic → finite algebra landing pad (zero topology/measure).

  This file is purely deterministic: it packages the “two-prime nondegeneracy”
  hypothesis into a Prop-class and shows it implies:
    ∃ x ∈ span(range c), F x ≠ 0

  Snapshot-robust:
  * no global/local instance search for XiPrimeWitnessW1Defs
  * no named-argument application to linear maps
  * does NOT assume `OffSeed` has a field `.t`
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Interface
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2Data_WireFromToeplitz
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2Data_RangeLemmas

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

open Hyperlocal.Transport
open scoped BigOperators

section

variable (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi)

/-- The wired linear map `F : Window 3 →ₗ[ℂ] Window 3` (Stage-2 wiring from Toeplitz). -/
def FWired (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi) :
    Window 3 →ₗ[ℂ] Window 3 := by
  classical
  letI := instXiPrimeWitnessW1Defs_xi_fromToeplitz (m := m) (s := s)
  exact (XiPrimeWitnessW1Defs.F
    (R := ℂ) (V := Window 3) (W := Window 3) (H := W1.Xi) (s := s))

/--
Single isolated “analytic cliff” hypothesis (Prop-class).

We *do not* hardcode `s.t` because your `OffSeed` has no field `.t`.
Instead we parameterize by a scalar `tval : ℂ` which later will be instantiated
by whatever your “t” actually is (likely `XiTransport.delta s` or similar).

If `tval ≠ 0`, at least one of the two prime generators has nonzero image under `F`.
-/
class XiPrimeWitnessW1TwoPrimeNondegeneracy
    (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi) (tval : ℂ) : Prop where
  nondeg :
    tval ≠ 0 →
      (FWired (m := m) (s := s) (wp2At m s) ≠ 0 ∨
       FWired (m := m) (s := s) (wp3At m s) ≠ 0)

/--
Deterministic consequence: if one generator image is nonzero, then `F` is nontrivial
on the span of `range c`.
-/
theorem exists_nonzero_on_span_range_c_of_or
    (h :
      FWired (m := m) (s := s) (wp2At m s) ≠ 0 ∨
      FWired (m := m) (s := s) (wp3At m s) ≠ 0) :
    ∃ x,
      x ∈ Submodule.span ℂ (Set.range (cWired (m := m) (s := s))) ∧
      FWired (m := m) (s := s) x ≠ 0 := by
  classical
  rcases h with h2 | h3
  · refine ⟨wp2At m s, ?_, h2⟩
    exact wp2At_mem_span_range_c (m := m) (s := s)
  · refine ⟨wp3At m s, ?_, h3⟩
    exact wp3At_mem_span_range_c (m := m) (s := s)

/--
Main landing lemma for the W1 gate, assuming the isolated Prop-class.
-/
theorem exists_nonzero_on_span_range_c_of_tval_ne_zero
    {tval : ℂ}
    [XiPrimeWitnessW1TwoPrimeNondegeneracy (m := m) (s := s) tval]
    (ht : tval ≠ 0) :
    ∃ x,
      x ∈ Submodule.span ℂ (Set.range (cWired (m := m) (s := s))) ∧
      FWired (m := m) (s := s) x ≠ 0 := by
  exact exists_nonzero_on_span_range_c_of_or (m := m) (s := s)
    (XiPrimeWitnessW1TwoPrimeNondegeneracy.nondeg (m := m) (s := s) (tval := tval) ht)

end

end W1
end XiPacket
end Targets
end Hyperlocal
