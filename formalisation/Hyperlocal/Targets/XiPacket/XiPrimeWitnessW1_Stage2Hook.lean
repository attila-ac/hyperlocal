/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Stage2Hook.lean

  W1 → Stage-2:
  If the Stage-2 map is nonzero on the span of prime windows, some prime witnesses nonvanishing.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Gate

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace W1

-- You will replace these with your actual types/definitions:
variable (ρ : Hyperlocal.OffSeed Xi)

-- V = "jet window space", W = "Gap output space"
variable {R : Type} [Semiring R]
variable {V : Type} [AddCommMonoid V] [Module R V]
variable {W : Type} [AddCommMonoid W] [Module R W]

-- Stage-2 pipeline map at seed ρ:
variable (Fρ : V →ₗ[R] W)

-- prime-window generator family at seed ρ:
variable (cρ : ℕ → V)

/-- Stage-2 W1 witness theorem (formal statement). -/
theorem exists_prime_witness_of_W1_gate
    [TAC.PrimeWitnessW1 (F := Fρ) (c := cρ)] :
    ∃ n : ℕ, Fρ (cρ n) ≠ 0 := by
  -- purely deterministic
  exact TAC.exists_generator_not_in_kernel_of_gate (F := Fρ) (c := cρ)

end W1

end XiPacket
end Targets
end Hyperlocal
