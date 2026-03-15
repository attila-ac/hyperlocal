/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Stage2Data_RangeLemmas.lean

  Deterministic lemmas about the Stage-2 data wiring from Toeplitz:
  show that the actual prime windows `wpAt m s p` lie in `Set.range c`,
  hence in the span of `Set.range c`.

  Snapshot-robust design:
  * Do NOT rely on a global `XiPrimeWitnessW1Defs` instance being found magically.
  * Instead, define `cWired m s` by installing the instance via `letI := ...`
    *inside* the def.

  Specialisations for `p=2,3` are retained because downstream finite-prime
  guardrail files still consume them.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Interface
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2Data_WireFromToeplitz

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

section

variable (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi)

/-- The wired generator family `c : PrimeIdx → Window 3` (actual-prime family). -/
def cWired (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi) :
    W1.PrimeIdx → Hyperlocal.Transport.Window 3 := by
  classical
  letI := instXiPrimeWitnessW1Defs_xi_fromToeplitz (m := m) (s := s)
  exact (XiPrimeWitnessW1Defs.c
    (R := ℂ) (V := Hyperlocal.Transport.Window 3) (W := Hyperlocal.Transport.Window 3)
    (H := W1.Xi) (s := s))

/-- The prime-2 index in `PrimeIdx`. -/
def p2 : W1.PrimeIdx := ⟨2, Nat.prime_two⟩

/-- The prime-3 index in `PrimeIdx`. -/
def p3 : W1.PrimeIdx := ⟨3, Nat.prime_three⟩

/-- Every actual prime window lies in the range of the wired generator family `c`. -/
lemma wpAt_mem_range_c (p : W1.PrimeIdx) :
    wpAt m s p.1 ∈ Set.range (cWired (m := m) (s := s)) := by
  refine ⟨p, ?_⟩
  simp [cWired, instXiPrimeWitnessW1Defs_xi_fromToeplitz]

/-- Nat-facing version of the previous lemma. -/
lemma wpAt_nat_mem_range_c (p : ℕ) (hp : Nat.Prime p) :
    wpAt m s p ∈ Set.range (cWired (m := m) (s := s)) := by
  simpa using (wpAt_mem_range_c (m := m) (s := s) (p := ⟨p, hp⟩))

/-- Hence every actual prime window lies in the ℂ-span of `Set.range c`. -/
lemma wpAt_mem_span_range_c (p : W1.PrimeIdx) :
    wpAt m s p.1 ∈ Submodule.span ℂ (Set.range (cWired (m := m) (s := s))) := by
  exact Submodule.subset_span (wpAt_mem_range_c (m := m) (s := s) (p := p))

/-- Nat-facing span version. -/
lemma wpAt_nat_mem_span_range_c (p : ℕ) (hp : Nat.Prime p) :
    wpAt m s p ∈ Submodule.span ℂ (Set.range (cWired (m := m) (s := s))) := by
  exact wpAt_mem_span_range_c (m := m) (s := s) (p := ⟨p, hp⟩)

/-- `wp2At m s` is in the range of the wired generator family `c`. -/
lemma wp2At_mem_range_c :
    wp2At m s ∈ Set.range (cWired (m := m) (s := s)) := by
  simpa [p2, wp2At] using (wpAt_mem_range_c (m := m) (s := s) (p := p2))

/-- `wp3At m s` is in the range of the wired generator family `c`. -/
lemma wp3At_mem_range_c :
    wp3At m s ∈ Set.range (cWired (m := m) (s := s)) := by
  simpa [p3, wp3At] using (wpAt_mem_range_c (m := m) (s := s) (p := p3))

/-- Hence `wp2At m s` lies in the ℂ-span of `Set.range c`. -/
lemma wp2At_mem_span_range_c :
    wp2At m s ∈ Submodule.span ℂ (Set.range (cWired (m := m) (s := s))) := by
  exact Submodule.subset_span (wp2At_mem_range_c (m := m) (s := s))

/-- Hence `wp3At m s` lies in the ℂ-span of `Set.range c`. -/
lemma wp3At_mem_span_range_c :
    wp3At m s ∈ Submodule.span ℂ (Set.range (cWired (m := m) (s := s))) := by
  exact Submodule.subset_span (wp3At_mem_range_c (m := m) (s := s))

end

end W1
end XiPacket
end Targets
end Hyperlocal
