/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceToeplitzLImpossibility.lean

  Guardrail lemma: with the current definitional `wc`, the *full-window* target
    toeplitzL 2 (coeffsNat3 c) (wc s) = 0
  forces c = 0 as soon as `s` is off-critical (δ ≠ 0).

  This prevents accidental regression to the too-strong axiom shape.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

namespace ToeplitzGuardrails

open ToeplitzLToRow3

/-- Closed-form coordinates of `wc` needed for the guardrail. -/
@[simp] lemma wc_apply_fin0 (s : Hyperlocal.OffSeed Xi) : wc s (0 : Fin 3) = 0 := by
  classical
  simp [wc_eq_basis, basisW3, e1, e2]

@[simp] lemma wc_apply_fin1 (s : Hyperlocal.OffSeed Xi) : wc s (1 : Fin 3) = 1 := by
  classical
  simp [wc_eq_basis, basisW3, e1, e2]

@[simp] lemma wc_apply_fin2 (s : Hyperlocal.OffSeed Xi) :
    wc s (2 : Fin 3) = (XiTransport.delta s : ℂ) := by
  classical
  simp [wc_eq_basis, basisW3, e1, e2]

/-!
Local simp helper.

Your local row-expansions for `toeplitzL` unfold through `shiftLₗ 2`.
On the Mathlib pin you’re on, `simp` will sometimes reduce products like
`coeffs 2 * (shiftLₗ 2 w) 2` via `mul_eq_zero`, leaving goals involving
`(shiftLₗ 2 w) 2 = 0`.  Make that fact available here explicitly.
-/

@[simp] lemma shiftLₗ_two_apply2_local (w : Window 3) :
    (shiftLₗ 2 w) (2 : Fin 3) = 0 := by
  classical
  have hrev2 : ((2 : Fin 3).rev) = (0 : Fin 3) := by decide
  have h :
      (shiftLₗ 2 w) (2 : Fin 3) =
        shiftR' (n := 2) (parity w) ((2 : Fin 3).rev) := by
    simp [shiftLₗ, parityₗ, shiftRₗ, LinearMap.comp_apply, parity]
  calc
    (shiftLₗ 2 w) (2 : Fin 3)
        = shiftR' (n := 2) (parity w) ((2 : Fin 3).rev) := h
    _   = shiftR' (n := 2) (parity w) (0 : Fin 3) := by simpa [hrev2]
    _   = 0 := by
          simpa using (shiftR'_zero (n := 2) (x := parity w))

/-!
Local (private) row-expansions for `toeplitzL 2` at Window length 3.

These are defined here to avoid depending on exported lemma names
(`toeplitzL_two_apply_fin1/fin2`) from other files.
-/

/-- Local row-0 expansion for `toeplitzL 2` at Window length 3. -/
private lemma toeplitzL_two_apply_fin0_local (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (0 : Fin 3) =
      (coeffs 0 * w 0 + coeffs 1 * w 1) + coeffs 2 * w 2 := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]

/-- Local row-1 expansion for `toeplitzL 2` at Window length 3. -/
private lemma toeplitzL_two_apply_fin1_local (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (1 : Fin 3) =
      (coeffs 0 * w 1) + (coeffs 1 * w 2) := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]

/-- Local row-2 expansion for `toeplitzL 2` at Window length 3. -/
private lemma toeplitzL_two_apply_fin2_local (coeffs : ℕ → ℂ) (w : Window 3) :
    (toeplitzL 2 coeffs w) (2 : Fin 3) = (coeffs 0 * w 2) := by
  classical
  simp [toeplitzL, shiftCombo, Finset.sum_range_succ, compPow,
        LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        add_assoc, add_left_comm, add_comm]

/--
**Impossibility (guardrail).**
For an off-critical seed `s`, if `toeplitzL 2 (coeffsNat3 c)` annihilates the *entire* window `wc s`,
then necessarily `c = 0`.
-/
theorem coeffsNat3_eq_zero_of_toeplitzL_two_wc_eq_zero
    (s : Hyperlocal.OffSeed Xi) (c : Fin 3 → ℝ)
    (h : toeplitzL 2 (coeffsNat3 c) (wc s) = 0) :
    c = 0 := by
  classical

  -- off-critical ⇒ δ ≠ 0
  have hδ : XiTransport.delta s ≠ 0 := by
    simpa [XiTransport.delta] using (sub_ne_zero.mpr s.hσ)

  have hδC : (XiTransport.delta s : ℂ) ≠ 0 := by
    intro hC
    have : XiTransport.delta s = 0 := by
      have := congrArg Complex.re hC
      simpa using this
    exact hδ this

  /- coord 2 ⇒ c0 = 0 -/
  have hz2 : (toeplitzL 2 (coeffsNat3 c) (wc s)) (2 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (2 : Fin 3)) h

  have hz2' : (coeffsNat3 c 0) * (wc s) (2 : Fin 3) = 0 := by
    have hz2a := hz2
    rw [toeplitzL_two_apply_fin2_local (coeffs := coeffsNat3 c) (w := wc s)] at hz2a
    simpa using hz2a

  have hz2'' : (c (0 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    simpa [coeffsNat3_nat0, wc_apply_fin2] using hz2'

  have hc0C : (c (0 : Fin 3) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hz2'' with h0 | h0
    · exact h0
    · exact False.elim (hδC h0)

  have hc0 : c (0 : Fin 3) = 0 := by
    have := congrArg Complex.re hc0C
    simpa using this

  /- coord 1 ⇒ c1 = 0 -/
  have hz1 : (toeplitzL 2 (coeffsNat3 c) (wc s)) (1 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (1 : Fin 3)) h

  have hz1' :
      (coeffsNat3 c 0) * (wc s) (1 : Fin 3) + (coeffsNat3 c 1) * (wc s) (2 : Fin 3) = 0 := by
    have hz1a := hz1
    rw [toeplitzL_two_apply_fin1_local (coeffs := coeffsNat3 c) (w := wc s)] at hz1a
    simpa using hz1a

  have hz1'' : (c (1 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    -- wc(1)=1, wc(2)=δ, and c0=0
    have : (c (0 : Fin 3) : ℂ) * (1 : ℂ) + (coeffsNat3 c 1) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [coeffsNat3_nat0, wc_apply_fin1, wc_apply_fin2] using hz1'
    simpa [coeffsNat3_nat1, hc0] using this

  have hc1C : (c (1 : Fin 3) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hz1'' with h0 | h0
    · exact h0
    · exact False.elim (hδC h0)

  have hc1 : c (1 : Fin 3) = 0 := by
    have := congrArg Complex.re hc1C
    simpa using this

  /- coord 0 ⇒ c2 = 0 -/
  have hz0 : (toeplitzL 2 (coeffsNat3 c) (wc s)) (0 : Fin 3) = 0 := by
    simpa using congrArg (fun x => x (0 : Fin 3)) h

  have hz0' :
      (coeffsNat3 c 0 * (wc s) (0 : Fin 3) + coeffsNat3 c 1 * (wc s) (1 : Fin 3)) +
        coeffsNat3 c 2 * (wc s) (2 : Fin 3) = 0 := by
    have hz0a := hz0
    rw [toeplitzL_two_apply_fin0_local (coeffs := coeffsNat3 c) (w := wc s)] at hz0a
    simpa using hz0a

  have hz0'' : (c (2 : Fin 3) : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    have :
        ((c (0 : Fin 3) : ℂ) * (0 : ℂ) + (c (1 : Fin 3) : ℂ) * (1 : ℂ)) +
          (coeffsNat3 c 2) * (XiTransport.delta s : ℂ) = 0 := by
      simpa [coeffsNat3_nat0, coeffsNat3_nat1,
             wc_apply_fin0, wc_apply_fin1, wc_apply_fin2] using hz0'
    simpa [coeffsNat3_nat2, hc0, hc1] using this

  have hc2C : (c (2 : Fin 3) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hz0'' with h0 | h0
    · exact h0
    · exact False.elim (hδC h0)

  have hc2 : c (2 : Fin 3) = 0 := by
    have := congrArg Complex.re hc2C
    simpa using this

  -- conclude c = 0
  funext i
  fin_cases i <;> simp [hc0, hc1, hc2]

/-- Convenience corollary: the old “full-window annihilation” axiom shape is impossible off-critical. -/
theorem no_nonzero_toeplitzL_annihilator_for_wc (s : Hyperlocal.OffSeed Xi) :
    ¬ ∃ c : Fin 3 → ℝ, c ≠ 0 ∧ toeplitzL 2 (coeffsNat3 c) (wc s) = 0 := by
  rintro ⟨c, hc, hT⟩
  have : c = 0 := coeffsNat3_eq_zero_of_toeplitzL_two_wc_eq_zero (s := s) (c := c) hT
  exact hc (by simpa [this])

end ToeplitzGuardrails
end Hyperlocal.Targets.XiPacket
