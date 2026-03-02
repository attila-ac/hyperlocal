/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy.lean

  Two-prime determinant nondegeneracy (AXIOM-FREE):

  Closed form for the two-prime 2×2 determinant at primes 2 and 3 built from
  PrimeTrigPacket.aCoeff / bCoeff:

    det23R(σ,t)
      = aCoeff σ t 2 * bCoeff σ t 3 - aCoeff σ t 3 * bCoeff σ t 2
      = pSigma σ 2 * pSigma σ 3 * sin(t * log(3/2)).

  Consequences:
    sin(t * log(3/2)) ≠ 0  ⇒  det23R(σ,t) ≠ 0
  and the same for the ℂ-cast determinant used downstream.

  NOTE:
  - No transport/jet/window imports.
  - Pure ℝ/ℂ algebra only (simp/ring + trig identity).
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

namespace W1

/-- The real 2×2 determinant at primes 2 and 3 in terms of aCoeff/bCoeff. -/
def det23R (σ t : ℝ) : ℝ :=
  aCoeff σ t (2 : ℝ) * bCoeff σ t (3 : ℝ)
    - aCoeff σ t (3 : ℝ) * bCoeff σ t (2 : ℝ)

/-- Convenience: `log(3/2) = log 3 - log 2` (using `Real.log_div`). -/
lemma log_three_div_two :
    Real.log ((3 : ℝ) / (2 : ℝ)) = Real.log (3 : ℝ) - Real.log (2 : ℝ) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  simpa using (Real.log_div h3 h2)

/--
Closed form:
  det23R(σ,t) = pSigma σ 2 * pSigma σ 3 * sin(t*log(3/2)).
-/
theorem det23R_eq_pSigma_mul_sin_log_ratio (σ t : ℝ) :
    det23R σ t
      =
    (pSigma σ (2 : ℝ)) * (pSigma σ (3 : ℝ)) *
      Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) := by
  classical

  -- Expand the PrimeTrigPacket coefficients.
  -- (aCoeff/bCoeff are real-valued; this is pure ℝ algebra.)
  unfold det23R aCoeff bCoeff

  -- Factor out the pSigma weights.
  have hfactor :
      pSigma σ (2 : ℝ) * Real.cos (t * Real.log (2 : ℝ)) *
            (pSigma σ (3 : ℝ) * Real.sin (t * Real.log (3 : ℝ)))
        -
      pSigma σ (3 : ℝ) * Real.cos (t * Real.log (3 : ℝ)) *
            (pSigma σ (2 : ℝ) * Real.sin (t * Real.log (2 : ℝ)))
        =
      (pSigma σ (2 : ℝ) * pSigma σ (3 : ℝ)) *
        (Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (3 : ℝ))
          - Real.cos (t * Real.log (3 : ℝ)) * Real.sin (t * Real.log (2 : ℝ))) := by
    ring

  -- Trig identity (re-ordered): cos(b)*sin(a) - cos(a)*sin(b) = sin(a-b).
  have htrig :
      (Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (3 : ℝ))
        - Real.cos (t * Real.log (3 : ℝ)) * Real.sin (t * Real.log (2 : ℝ)))
        =
      Real.sin (t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)) := by
    -- `Real.sin_sub a b : sin(a-b) = sin a * cos b - cos a * sin b`
    have h := Real.sin_sub (t * Real.log (3 : ℝ)) (t * Real.log (2 : ℝ))
    -- rewrite `sin a * cos b` as `cos b * sin a`, then flip.
    have :
        Real.sin (t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ))
          =
        Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (3 : ℝ))
          - Real.cos (t * Real.log (3 : ℝ)) * Real.sin (t * Real.log (2 : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact this.symm

  -- Rewrite the difference of logs into the log-ratio.
  have hlog :
      t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)
        =
      t * Real.log ((3 : ℝ) / (2 : ℝ)) := by
    calc
      t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)
          = t * (Real.log (3 : ℝ) - Real.log (2 : ℝ)) := by ring
      _   = t * Real.log ((3 : ℝ) / (2 : ℝ)) := by
            simpa using congrArg (fun x => t * x) (log_three_div_two).symm

  -- Assemble.
  calc
    pSigma σ (2 : ℝ) * Real.cos (t * Real.log (2 : ℝ)) *
          (pSigma σ (3 : ℝ) * Real.sin (t * Real.log (3 : ℝ)))
      -
    pSigma σ (3 : ℝ) * Real.cos (t * Real.log (3 : ℝ)) *
          (pSigma σ (2 : ℝ) * Real.sin (t * Real.log (2 : ℝ)))
        =
      (pSigma σ (2 : ℝ) * pSigma σ (3 : ℝ)) *
        (Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (3 : ℝ))
          - Real.cos (t * Real.log (3 : ℝ)) * Real.sin (t * Real.log (2 : ℝ))) := by
      simpa using hfactor
  _ =
      (pSigma σ (2 : ℝ) * pSigma σ (3 : ℝ)) *
        Real.sin (t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)) := by
      simp [htrig]
  _ =
      (pSigma σ (2 : ℝ) * pSigma σ (3 : ℝ)) *
        Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) := by
      simp [hlog]
  _ =
      (pSigma σ (2 : ℝ)) * (pSigma σ (3 : ℝ)) *
        Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) := by
      ring

/-- Nonvanishing criterion in ℝ: det23R ≠ 0 if `sin(t*log(3/2)) ≠ 0`. -/
theorem det23R_ne_zero_of_sin_log_ratio_ne_zero
    (σ t : ℝ)
    (hsin : Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) ≠ 0) :
    det23R σ t ≠ 0 := by
  have hp2 : pSigma σ (2 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (2 : ℝ)))
  have hp3 : pSigma σ (3 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (3 : ℝ)))

  have hform := det23R_eq_pSigma_mul_sin_log_ratio (σ := σ) (t := t)

  -- Product nonzero, hence determinant nonzero.
  have hprod :
      (pSigma σ (2 : ℝ)) * (pSigma σ (3 : ℝ)) *
        Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp2 hp3) hsin

  -- Use `simpa` (NOT `simp ... using`) to rewrite det23R into the closed form.
  simpa [hform] using hprod

/-- The same determinant but viewed in ℂ (the exact shape Stage-2 uses). -/
theorem det23C_eq_of_det23R (σ t : ℝ) :
    ((det23R σ t : ℝ) : ℂ)
      =
    (aCoeff σ t (2 : ℝ) : ℂ) * (bCoeff σ t (3 : ℝ) : ℂ)
      -
    (aCoeff σ t (3 : ℝ) : ℂ) * (bCoeff σ t (2 : ℝ) : ℂ) := by
  simp [det23R]

/-- Complex determinant nonzero if the sine-factor is nonzero (ready for Stage-2). -/
theorem det23C_ne_zero_of_sin_log_ratio_ne_zero
    (σ t : ℝ)
    (hsin : Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) ≠ 0) :
    (aCoeff σ t (2 : ℝ) : ℂ) * (bCoeff σ t (3 : ℝ) : ℂ)
      -
    (aCoeff σ t (3 : ℝ) : ℂ) * (bCoeff σ t (2 : ℝ) : ℂ) ≠ 0 := by
  have hR : det23R σ t ≠ 0 :=
    det23R_ne_zero_of_sin_log_ratio_ne_zero (σ := σ) (t := t) hsin
  intro hC
  have hC' : ((det23R σ t : ℝ) : ℂ) = 0 := by
    simpa [det23C_eq_of_det23R (σ := σ) (t := t)] using hC
  have hR0 : (det23R σ t : ℝ) = 0 := by
    exact_mod_cast hC'
  exact hR hR0

/--
Guardrails-facing micro-gate:
if the ℂ-cast sine-factor is nonzero, then the ℂ determinant is nonzero.
-/
theorem det23C_ne_zero_of_tval_ne_zero
    (σ t : ℝ)
    (htv :
      ((Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    (aCoeff σ t (2 : ℝ) : ℂ) * (bCoeff σ t (3 : ℝ) : ℂ)
      -
    (aCoeff σ t (3 : ℝ) : ℂ) * (bCoeff σ t (2 : ℝ) : ℂ) ≠ 0 := by
  have hsin : Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) ≠ 0 := by
    intro h0
    apply htv
    simpa [h0]
  exact det23C_ne_zero_of_sin_log_ratio_ne_zero (σ := σ) (t := t) hsin

end W1

end XiPacket
end Targets
end Hyperlocal
