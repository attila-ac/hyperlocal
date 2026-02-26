/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Stage2Data_RangeLemmas.lean

  Deterministic lemmas about the Stage-2 data wiring from Toeplitz:
  show that the jet-pivot prime windows `wp2At` and `wp3At` lie in `Set.range c`,
  hence in the span of `Set.range c`.

  Snapshot-robust design:
  * Do NOT rely on a `local instance : XiPrimeWitnessW1Defs ... := ...` being found globally.
  * Instead, define `cWired m s` by installing the instance via `letI := ...` *inside* the def.
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

/-- The wired generator family `c : PrimeIdx → Window 3` (Stage-2 wiring from Toeplitz). -/
def cWired (m : ℕ) (s : Hyperlocal.OffSeed W1.Xi) :
    W1.PrimeIdx → Hyperlocal.Transport.Window 3 := by
  classical
  -- install the Stage-2 wired instance locally
  letI := instXiPrimeWitnessW1Defs_xi_fromToeplitz (m := m) (s := s)
  exact (XiPrimeWitnessW1Defs.c
    (R := ℂ) (V := Hyperlocal.Transport.Window 3) (W := Hyperlocal.Transport.Window 3)
    (H := W1.Xi) (s := s))

/-- The prime-2 index in `PrimeIdx`. -/
def p2 : W1.PrimeIdx := ⟨2, Nat.prime_two⟩

/-- The prime-3 index in `PrimeIdx`. -/
def p3 : W1.PrimeIdx := ⟨3, Nat.prime_three⟩

/-- `wp2At m s` is in the range of the wired generator family `c`. -/
lemma wp2At_mem_range_c :
    wp2At m s ∈ Set.range (cWired (m := m) (s := s)) := by
  classical
  refine ⟨p2, ?_⟩
  -- Unfolding `cWired` exposes the `letI` instance; `simp` then selects the p=2 branch.
  simp [cWired, p2, instXiPrimeWitnessW1Defs_xi_fromToeplitz]

/-- `wp3At m s` is in the range of the wired generator family `c`. -/
lemma wp3At_mem_range_c :
    wp3At m s ∈ Set.range (cWired (m := m) (s := s)) := by
  classical
  refine ⟨p3, ?_⟩
  simp [cWired, p3, instXiPrimeWitnessW1Defs_xi_fromToeplitz]

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
