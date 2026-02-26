/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Gate.lean

  W1 gate (cycle-safe):
  A single Prop-class asserting "F is not identically zero on the span of the generators".

  This file is purely algebraic and can be imported anywhere.
-/

import Hyperlocal.Targets.XiPacket.TACPrimeWitness_W1

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

variable {R : Type} [Semiring R]
variable {V : Type} [AddCommMonoid V] [Module R V]
variable {W : Type} [AddCommMonoid W] [Module R W]

/-- W1 gate: `F` is nonzero somewhere on `span(range c)`. -/
class PrimeWitnessW1 (F : V →ₗ[R] W) (c : ℕ → V) : Prop :=
(nonzero_on_span : ∃ y ∈ Submodule.span R (Set.range c), F y ≠ 0)

/-- W1 extraction: the gate implies some generator escapes the kernel. -/
theorem exists_generator_not_in_kernel_of_gate
    (F : V →ₗ[R] W) (c : ℕ → V) [PrimeWitnessW1 (F := F) (c := c)] :
    ∃ n : ℕ, F (c n) ≠ 0 := by
  -- uses your proven deterministic lemma
  exact
    exists_generator_not_in_kernel_of_not_eq_zero_on_span
      (F := F) (c := c) (PrimeWitnessW1.nonzero_on_span (F := F) (c := c))

end TAC
end XiPacket
end Targets
end Hyperlocal
