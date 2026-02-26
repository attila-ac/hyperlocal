/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1TrueAnalytic.lean

  TRUE-ANALYTIC landing pad for the Way 1 (W1) prime-witness backbone.

  This file intentionally does NOT prove the analytic nondegeneracy.
  It:
  * fixes the target function to the concrete Riemann ξ implementation `Hyperlocal.xi`,
  * re-exports the W1 gate,
  * provides the deterministic consequence used by downstream endpoints.
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace W1

section

variable {R V W : Type}
variable [Semiring R]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

/-- Notation: the concrete ξ target. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Specialization of the W1 gate to ξ. -/
abbrev XiPrimeWitnessW1TrueAnalytic (s : Hyperlocal.OffSeed Xi) : Type :=
  W1.XiPrimeWitnessW1 (R := R) (V := V) (W := W) (H := Xi) s

/-- Downstream-facing lemma: from a ξ-W1 gate instance, get a prime with nonzero image. -/
theorem exists_prime_witness_xi
    {s : Hyperlocal.OffSeed Xi}
    [XiPrimeWitnessW1TrueAnalytic (R := R) (V := V) (W := W) s] :
    ∃ p : W1.PrimeIdx,
      (W1.XiPrimeWitnessW1.F (s := s) (R := R) (V := V) (W := W) (H := Xi))
        ((W1.XiPrimeWitnessW1.c (s := s) (R := R) (V := V) (W := W) (H := Xi)) p) ≠ 0 := by
  -- `OffSeed` already carries the hypothesis `t ≠ 0` as `s.ht`.
  exact W1.exists_prime_witness (R := R) (V := V) (W := W) (H := Xi) (s := s) s.ht

end

end W1
end XiPacket
end Targets
end Hyperlocal
