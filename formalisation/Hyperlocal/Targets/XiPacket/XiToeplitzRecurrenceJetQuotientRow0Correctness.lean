/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Correctness.lean

  NEXT MUST-DO:
  Replace the two remaining row-0 operator-output axioms by theorems.

  Design goal:
  * This file is the ONLY place where ξ-analytic semantics should enter the
    Toeplitz/recurrence gate.
  * Everything below compiles immediately, and there is exactly ONE `sorry`
    placeholder: `xiJetQuotRow0Out`.
-/

import Hyperlocal.Core
import Hyperlocal.MinimalModel
import Hyperlocal.Cancellation.Recurrence
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperator
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators
open Hyperlocal
open Hyperlocal.Transport
open ToeplitzLToRow3

/-!
  ## Single semantic output (row-0 only)

  We package the *only* ξ-semantic obligation you still need at the Toeplitz gate:

  There exists a nonzero real stencil `c : Fin 3 → ℝ` such that row-0 of
  `toeplitzL 2 (coeffsNat3 c)` vanishes on each of the relevant windows
  (`w0`, `wc`, `wp2`, `wp3`).

  Everything downstream (row-stencil → ell=0 → Move-4 plumbing) is algebraic.
-/

/--
The single ξ-semantic deliverable at this layer (row-0 constraints only).

NOTE: This must be `Type`, not `Prop`, because it contains data (`c`).
If you later want a Prop wrapper, use `Nonempty (XiJetQuotRow0Out s)`.
-/
structure XiJetQuotRow0Out (s : Hyperlocal.OffSeed Xi) : Type where
  c    : Fin 3 → ℝ
  hc   : c ≠ 0
  hw0  : (toeplitzL 2 (coeffsNat3 c) (w0 s))  (0 : Fin 3) = 0
  hwc  : (toeplitzL 2 (coeffsNat3 c) (wc s))  (0 : Fin 3) = 0
  hwp2 : (toeplitzL 2 (coeffsNat3 c) (wp2 s)) (0 : Fin 3) = 0
  hwp3 : (toeplitzL 2 (coeffsNat3 c) (wp3 s)) (0 : Fin 3) = 0

/--
THE ONLY remaining semantic cliff (one location, one goal).

This must be a `def` (not a `theorem`), because `XiJetQuotRow0Out s : Type`.
-/
noncomputable def xiJetQuotRow0Out (s : Hyperlocal.OffSeed Xi) : XiJetQuotRow0Out s := by
  -- TODO: ξ-specific analytic proof lives here.
  -- Keep EVERYTHING else axiom-free.
  sorry

/-- Convenience: extracted stencil. -/
def cJet (s : Hyperlocal.OffSeed Xi) : Fin 3 → ℝ :=
  (xiJetQuotRow0Out (s := s)).c

lemma cJet_ne_zero (s : Hyperlocal.OffSeed Xi) : cJet s ≠ 0 :=
  (xiJetQuotRow0Out (s := s)).hc

lemma row0_w0 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (w0 s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hw0

lemma row0_wc (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (wc s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hwc

lemma row0_wp2 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (wp2 s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hwp2

lemma row0_wp3 (s : Hyperlocal.OffSeed Xi) :
    (toeplitzL 2 (coeffsNat3 (cJet s)) (wp3 s)) (0 : Fin 3) = 0 :=
  (xiJetQuotRow0Out (s := s)).hwp3

/-- (Corrected) p=2: theorem form (replaces the old axiom). -/
theorem xiJetQuotToeplitzL_row0_fromOperator2 (s : Hyperlocal.OffSeed Xi) :
  ∃ c2 : Fin 3 → ℝ,
    c2 ≠ 0 ∧
    (toeplitzL 2 (coeffsNat3 c2) (w0 s)) (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c2) (wc s)) (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c2) (wp2 s)) (0 : Fin 3) = 0 := by
  refine ⟨cJet s, cJet_ne_zero (s := s), ?_, ?_, ?_⟩
  · simpa [cJet] using row0_w0 (s := s)
  · simpa [cJet] using row0_wc (s := s)
  · simpa [cJet] using row0_wp2 (s := s)

/-- (Corrected) p=3: theorem form (replaces the old axiom). -/
theorem xiJetQuotToeplitzL_row0_fromOperator3 (s : Hyperlocal.OffSeed Xi) :
  ∃ c3 : Fin 3 → ℝ,
    c3 ≠ 0 ∧
    (toeplitzL 2 (coeffsNat3 c3) (w0 s)) (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c3) (wc s)) (0 : Fin 3) = 0 ∧
    (toeplitzL 2 (coeffsNat3 c3) (wp3 s)) (0 : Fin 3) = 0 := by
  refine ⟨cJet s, cJet_ne_zero (s := s), ?_, ?_, ?_⟩
  · simpa [cJet] using row0_w0 (s := s)
  · simpa [cJet] using row0_wc (s := s)
  · simpa [cJet] using row0_wp3 (s := s)

end Hyperlocal.Targets.XiPacket
