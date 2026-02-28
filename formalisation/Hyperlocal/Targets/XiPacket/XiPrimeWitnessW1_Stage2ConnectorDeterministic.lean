/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Stage2ConnectorDeterministic.lean

  Deterministic Stage-2 connector (W1):

  Guardrails-facing API:
    If FWired(wp2At)=0 and FWired(wp3At)=0 and tval ≠ 0,
    manufacture ∃ c ≠ 0, toeplitzL 2 (coeffsNat3 c) (wc s) = 0.

  Purely finite algebra (no analytic content).

  UPDATE (2026-02-27+):
  - We removed the det23 axiom. This file now *reduces* the needed 2×2 determinant
    to the explicit sine micro-gate via the axiom-free closed form in
    `XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy.lean`.
-/

import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_FWiredFromOpZeroAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowJetPivot_wpAtExpand
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy

import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

-- IMPORTANT: wp2At_apply/wp3At_apply live here
open JetPivot

namespace W1

/-- Convenience: view `toeplitzL 2 coeffs` as a `LinearMap` so we can use `map_add/map_smul`. -/
private def toeplitzLM (coeffs : ℕ → ℂ) : (Transport.Window 3) →ₗ[ℂ] (Transport.Window 3) :=
  toeplitzL 2 coeffs

/--
Core elimination lemma over `ℂ`:

Assume
  L(w0)=0, L(wp2)=0, L(wp3)=0
and the window expansions
  wp2 = w0 + A2•wc + B2•ws
  wp3 = w0 + A3•wc + B3•ws
with det := A2*B3 - A3*B2 ≠ 0.

Then L(wc)=0.
-/
private lemma wc_eq_zero_of_three_zeros_and_det
    (coeffs : ℕ → ℂ)
    (w0 wc ws wp2 wp3 : Transport.Window 3)
    (A2 B2 A3 B3 : ℂ)
    (hw0  : toeplitzL 2 coeffs w0  = 0)
    (hwp2 : toeplitzL 2 coeffs wp2 = 0)
    (hwp3 : toeplitzL 2 coeffs wp3 = 0)
    (hwp2exp : wp2 = w0 + A2 • wc + B2 • ws)
    (hwp3exp : wp3 = w0 + A3 • wc + B3 • ws)
    (hdet : A2 * B3 - A3 * B2 ≠ 0) :
    toeplitzL 2 coeffs wc = 0 := by
  classical
  let L : (Transport.Window 3) →ₗ[ℂ] (Transport.Window 3) := toeplitzLM coeffs

  have eq2 : A2 • (L wc) + B2 • (L ws) = 0 := by
    have hlin :
        L wp2 = L w0 + (A2 • (L wc) + B2 • (L ws)) := by
      calc
        L wp2 = L (w0 + A2 • wc + B2 • ws) := by
          simpa [hwp2exp]
        _ = L w0 + L (A2 • wc + B2 • ws) := by
          simp [map_add, add_assoc]
        _ = L w0 + (A2 • (L wc) + B2 • (L ws)) := by
          simp [map_add, map_smul]
    have hwp2' : L wp2 = 0 := by simpa [L, toeplitzLM] using hwp2
    have hw0' : L w0 = 0 := by simpa [L, toeplitzLM] using hw0
    have : L w0 + (A2 • (L wc) + B2 • (L ws)) = 0 := by
      simpa [hlin] using hwp2'
    simpa [hw0'] using this

  have eq3 : A3 • (L wc) + B3 • (L ws) = 0 := by
    have hlin :
        L wp3 = L w0 + (A3 • (L wc) + B3 • (L ws)) := by
      calc
        L wp3 = L (w0 + A3 • wc + B3 • ws) := by
          simpa [hwp3exp]
        _ = L w0 + L (A3 • wc + B3 • ws) := by
          simp [map_add, add_assoc]
        _ = L w0 + (A3 • (L wc) + B3 • (L ws)) := by
          simp [map_add, map_smul]
    have hwp3' : L wp3 = 0 := by simpa [L, toeplitzLM] using hwp3
    have hw0' : L w0 = 0 := by simpa [L, toeplitzLM] using hw0
    have : L w0 + (A3 • (L wc) + B3 • (L ws)) = 0 := by
      simpa [hlin] using hwp3'
    simpa [hw0'] using this

  have hdet_smul : (A2 * B3 - A3 * B2) • (L wc) = 0 := by
    have hcomb :
        B3 • (A2 • (L wc) + B2 • (L ws))
          - B2 • (A3 • (L wc) + B3 • (L ws)) = 0 := by
      simp [eq2, eq3]

    have hcomb_exp :
        (B3 * A2) • (L wc) + (B3 * B2) • (L ws)
          - ((B2 * A3) • (L wc) + (B2 * B3) • (L ws)) = 0 := by
      simpa [sub_eq_add_neg, smul_add, smul_smul, mul_assoc, add_assoc, add_left_comm, add_comm]
        using hcomb

    have hwc_only :
        (B3 * A2) • (L wc) - (B2 * A3) • (L wc) = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using hcomb_exp

    have hwc_det :
        (A2 * B3 - A3 * B2) • (L wc) = 0 := by
      have hwc_only' :
          (A2 * B3) • (L wc) - (A3 * B2) • (L wc) = 0 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hwc_only
      simpa using (show (A2 * B3 - A3 * B2) • (L wc) = 0 from by
        simpa [sub_smul] using hwc_only')

    exact hwc_det

  rcases smul_eq_zero.mp hdet_smul with hdet0 | hwc
  · exact False.elim (hdet (by simpa using hdet0))
  · exact hwc

/--
**Guardrails-facing API**:

If both wired outputs vanish at wp2/wp3, and `tval ≠ 0` where

  tval := ((sin(t(s) * log(3/2)) : ℝ) : ℂ),

then we manufacture a concrete nonzero real stencil `c` and prove it annihilates `wc s`.

The determinant nondegeneracy is discharged via the axiom-free closed form:
  `W1.det23C_ne_zero_of_tval_ne_zero`.
-/
theorem toeplitzL_wc_of_Fwp2_Fwp3_zero
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    (h2 : (FWired (m := m) (s := s)) (wp2At m s) = 0)
    (h3 : (FWired (m := m) (s := s)) (wp3At m s) = 0)
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧ toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (wc s) = 0 := by
  classical

  -- semantic OpZeroAtOrder package gives w0/wp2/wp3 annihilation for the JetQuot Toeplitz operator
  let Hop : XiJetQuotOpZeroAtOrder m s := xiJetQuotOpZeroAtOrder (m := m) (s := s)

  -- Define the real stencil: take Re of the first 3 Toeplitz coefficients
  let c : Fin 3 → ℝ := fun i => (JetQuotOp.aRk1 s i.1).re

  have hc : c ≠ 0 := by
    intro hcz
    have : c (2 : Fin 3) = 0 := by simpa [hcz]
    have h2re : (JetQuotOp.aRk1 s 2).re = (-2 : ℝ) := by
      simpa [JetQuotOp.aRk1_nat2_eq_neg_two (s := s)]
    simpa [c, h2re] using this

  -- Show coeffsNat3(c) agrees with aRk1(s) on {0,1,2}.
  have hcoeff0 : ToeplitzLToRow3.coeffsNat3 c 0 = JetQuotOp.aRk1 s 0 := by
    have hre : ((JetQuotOp.aRk1 s 0).re : ℂ) = JetQuotOp.aRk1 s 0 := by
      apply Complex.ext <;> simp [JetQuotOp.aRk1_im0 (s := s)]
    simpa [ToeplitzLToRow3.coeffsNat3, c, hre]

  have hcoeff1 : ToeplitzLToRow3.coeffsNat3 c 1 = JetQuotOp.aRk1 s 1 := by
    have hre : ((JetQuotOp.aRk1 s 1).re : ℂ) = JetQuotOp.aRk1 s 1 := by
      apply Complex.ext <;> simp [JetQuotOp.aRk1_im1 (s := s)]
    simpa [ToeplitzLToRow3.coeffsNat3, c, hre]

  have hcoeff2 : ToeplitzLToRow3.coeffsNat3 c 2 = JetQuotOp.aRk1 s 2 := by
    have hre : ((JetQuotOp.aRk1 s 2).re : ℂ) = JetQuotOp.aRk1 s 2 := by
      apply Complex.ext <;> simp [JetQuotOp.aRk1_im2 (s := s)]
    simpa [ToeplitzLToRow3.coeffsNat3, c, hre]

  -- Toeplitz operator with coeffsNat3(c) equals Toeplitz operator with aRk1(s), since only 0/1/2 matter.
  have htoe_eq (w : Transport.Window 3) :
      toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) w
        = toeplitzL 2 (JetQuotOp.aRk1 s) w := by
    funext i
    fin_cases i
    · simp [toeplitzL_two_apply_fin0, hcoeff0, hcoeff1, hcoeff2]
    · simp [toeplitzL_two_apply_fin1, hcoeff0, hcoeff1, hcoeff2]
    · simp [toeplitzL_two_apply_fin2, hcoeff0, hcoeff1, hcoeff2]

  -- Turn w0/wp2/wp3 annihilation of aRk1 into annihilation for this concrete stencil.
  have hw0 : toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (w0At m s) = 0 := by
    simpa [htoe_eq (w := w0At m s)] using Hop.hop_w0At

  have hwp2 : toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (wp2At m s) = 0 := by
    simpa [htoe_eq (w := wp2At m s)] using Hop.hop_wp2At

  have hwp3 : toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (wp3At m s) = 0 := by
    simpa [htoe_eq (w := wp3At m s)] using Hop.hop_wp3At

  -- expansions
  let A2 : ℂ := (aCoeff (σ s) (t s) (2 : ℝ) : ℂ)
  let B2 : ℂ := (bCoeff (σ s) (t s) (2 : ℝ) : ℂ)
  let A3 : ℂ := (aCoeff (σ s) (t s) (3 : ℝ) : ℂ)
  let B3 : ℂ := (bCoeff (σ s) (t s) (3 : ℝ) : ℂ)

  have hwp2exp :
      wp2At m s = w0At m s + A2 • wc s + B2 • ws s := by
    funext i
    simp [wp2At_apply, A2, B2, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm]

  have hwp3exp :
      wp3At m s = w0At m s + A3 • wc s + B3 • ws s := by
    funext i
    simp [wp3At_apply, A3, B3, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm]

  -- determinant nonzero: now **directly** from `tval ≠ 0`
  have hdet : A2 * B3 - A3 * B2 ≠ 0 := by
    simpa [A2, B2, A3, B3, sub_eq_add_neg] using
      (W1.det23C_ne_zero_of_tval_ne_zero (σ := σ s) (t := t s) htv)

  have hwc :
      toeplitzL 2 (ToeplitzLToRow3.coeffsNat3 c) (wc s) = 0 := by
    simpa [A2, B2, A3, B3] using
      (wc_eq_zero_of_three_zeros_and_det
        (coeffs := ToeplitzLToRow3.coeffsNat3 c)
        (w0 := w0At m s) (wc := wc s) (ws := ws s)
        (wp2 := wp2At m s) (wp3 := wp3At m s)
        (A2 := A2) (B2 := B2) (A3 := A3) (B3 := B3)
        (hw0 := hw0) (hwp2 := hwp2) (hwp3 := hwp3)
        (hwp2exp := hwp2exp) (hwp3exp := hwp3exp)
        (hdet := hdet))

  exact ⟨c, hc, hwc⟩

end W1

end XiPacket
end Targets
end Hyperlocal
