/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_FromStage2Data.lean

  Way 1 (W1) backbone: wiring adapter.

  Purpose:
  Split the W1 gate into:
    * a "Stage-2 data" provider (the concrete generator family `c` and linear map `F`), and
    * a "true-analytic nontriviality" provider (the only remaining analytic cliff).

  Then repackage them into the existing `W1.XiPrimeWitnessW1` class.

  This file is cycle-safe and purely algebraic: it imports only the W1 gate.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1

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

/--
Stage-2 *data* for W1: concrete prime generators `c` and the Stage-2 linear map `F`.

This is intentionally `Type`-valued (it carries data).
-/
class XiPrimeWitnessW1Stage2Data (s : Hyperlocal.OffSeed H) : Type where
  /-- Generator family indexed by primes. -/
  c : W1.PrimeIdx → V
  /-- Stage-2 linear map (finite-dimensional pipeline). -/
  F : V →ₗ[R] W

/--
True-analytic W1 cliff, stated against the Stage-2 data.

This is also `Type`-valued: we want to be able to project it without fighting
Prop-class restrictions in downstream wiring.

NOTE: the only content here is the nontriviality-on-span statement.
-/
class XiPrimeWitnessW1Nontrivial
    (s : Hyperlocal.OffSeed H)
    [XiPrimeWitnessW1Stage2Data (R := R) (V := V) (W := W) (H := H) s] : Type where
  /-- Nontriviality on the prime span: the analytic cliff. -/
  nontrivial (ht : s.ρ.im ≠ 0) :
      ∃ x : V,
        x ∈ Submodule.span R
              (Set.range (XiPrimeWitnessW1Stage2Data.c
                (s := s) (R := R) (V := V) (W := W) (H := H))) ∧
        (XiPrimeWitnessW1Stage2Data.F
          (s := s) (R := R) (V := V) (W := W) (H := H)) x ≠ 0

/--
Adapter: Stage-2 data + nontriviality ⇒ the unified W1 gate.

Once you have `[XiPrimeWitnessW1Stage2Data s]` and `[XiPrimeWitnessW1Nontrivial s]`,
you get `[XiPrimeWitnessW1 s]` for free.
-/
instance instXiPrimeWitnessW1_of_stage2Data
    (s : Hyperlocal.OffSeed H)
    [XiPrimeWitnessW1Stage2Data (R := R) (V := V) (W := W) (H := H) s]
    [XiPrimeWitnessW1Nontrivial (R := R) (V := V) (W := W) (H := H) s] :
    W1.XiPrimeWitnessW1 (R := R) (V := V) (W := W) (H := H) s where
  c := XiPrimeWitnessW1Stage2Data.c (s := s) (R := R) (V := V) (W := W) (H := H)
  F := XiPrimeWitnessW1Stage2Data.F (s := s) (R := R) (V := V) (W := W) (H := H)
  nontrivial ht :=
    XiPrimeWitnessW1Nontrivial.nontrivial
      (s := s) (R := R) (V := V) (W := W) (H := H) ht

end

end W1
end XiPacket
end Targets
end Hyperlocal
