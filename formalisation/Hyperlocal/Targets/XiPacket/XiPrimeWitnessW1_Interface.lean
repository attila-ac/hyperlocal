/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Interface.lean

  Way 1 (W1) backbone: split the “data” (c,F) from the “analytic cliff” (nontrivial).

  Snapshot note:
  Avoid `Mathlib.LinearAlgebra.Basic` (not present in your Lean 4.23 rc2 snapshot).
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_LinAlg
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

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

variable {H : ℂ → ℂ}

/-- Prime index type used for W1: the subtype of natural primes. -/
abbrev PrimeIdx : Type := {p : ℕ // Nat.Prime p}

/--
W1 “definitions” layer (wiring-only):
provide the generator family `c` and the Stage-2 linear map `F`.
This is intentionally `Type`, so you can construct it definitionally.
-/
class XiPrimeWitnessW1Defs (s : Hyperlocal.OffSeed H) : Type where
  /-- Generator family indexed by primes. -/
  c : PrimeIdx → V
  /-- Stage-2 linear map (finite-dimensional pipeline). -/
  F : V →ₗ[R] W

/--
W1 “gate” (single analytic cliff):
assuming the definitions `c` and `F` are in place, assert that (t≠0) implies
`F` is not identically zero on the span of the prime generators.
-/
class XiPrimeWitnessW1Gate (s : Hyperlocal.OffSeed H)
    [XiPrimeWitnessW1Defs (R := R) (V := V) (W := W) s] : Prop where
  /-- Nontriviality on the prime span (the analytic cliff). -/
  nontrivial (ht : s.ρ.im ≠ 0) :
    ∃ x : V,
      x ∈ Submodule.span R (Set.range (XiPrimeWitnessW1Defs.c (R := R) (V := V) (W := W) (s := s))) ∧
      (XiPrimeWitnessW1Defs.F (R := R) (V := V) (W := W) (s := s)) x ≠ 0

/--
Deterministic consequence (pure lin alg):
from the W1 gate, get an explicit prime witness `p` with `F (c p) ≠ 0`.
-/
theorem exists_prime_witness_of_gate
    {s : Hyperlocal.OffSeed H}
    [XiPrimeWitnessW1Defs (R := R) (V := V) (W := W) s]
    [XiPrimeWitnessW1Gate (R := R) (V := V) (W := W) s]
    (ht : s.ρ.im ≠ 0) :
    ∃ p : PrimeIdx,
      (XiPrimeWitnessW1Defs.F (R := R) (V := V) (W := W) (s := s))
        ((XiPrimeWitnessW1Defs.c (R := R) (V := V) (W := W) (s := s)) p) ≠ 0 := by
  classical
  rcases (XiPrimeWitnessW1Gate.nontrivial (R := R) (V := V) (W := W) (s := s) ht) with
    ⟨x, hxspan, hxne⟩
  simpa using
    (exists_generator_of_exists_span_ne_zero
      (F := XiPrimeWitnessW1Defs.F (R := R) (V := V) (W := W) (s := s))
      (v := XiPrimeWitnessW1Defs.c (R := R) (V := V) (W := W) (s := s))
      (hspan := ⟨x, hxspan, hxne⟩))

end

end W1
end XiPacket
end Targets
end Hyperlocal
