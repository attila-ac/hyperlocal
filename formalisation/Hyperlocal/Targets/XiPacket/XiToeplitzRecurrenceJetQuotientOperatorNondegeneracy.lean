/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy.lean

  Cycle-safe nondegeneracy boundary (AXIOM-FREE):

  Exact closed form for the two-prime 2×2 determinant built from
  PrimeTrigPacket.aCoeff/bCoeff at p=2,3:

    det23R(σ,t) = aCoeff σ t 2 * bCoeff σ t 3 - aCoeff σ t 3 * bCoeff σ t 2
                = pSigma σ 2 * pSigma σ 3 * sin(t * log(3/2)).

  Consequently:
    sin(t * log(3/2)) ≠ 0  ⇒  det23R(σ,t) ≠ 0
  and the same for the ℂ-cast determinant used downstream.

  NOTE:
  - This file intentionally does NOT mention XiTransport.delta.
    The determinant depends on the height `t`.
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
  -- expand aCoeff/bCoeff; do the trig identity in ℝ
  unfold det23R aCoeff bCoeff

  -- trig core: sin(x-y)=sin x * cos y - cos x * sin y
  have hsin_sub :
      Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (3 : ℝ))
        - Real.cos (t * Real.log (3 : ℝ)) * Real.sin (t * Real.log (2 : ℝ))
        =
      Real.sin (t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)) := by
    have h := Real.sin_sub (t * Real.log (3 : ℝ)) (t * Real.log (2 : ℝ))
    have :
        Real.sin (t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ))
          =
        Real.cos (t * Real.log (2 : ℝ)) * Real.sin (t * Real.log (3 : ℝ))
          - Real.cos (t * Real.log (3 : ℝ)) * Real.sin (t * Real.log (2 : ℝ)) := by
      -- h : sin(x - y) = sin x * cos y - cos x * sin y
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact this.symm

  -- log rewrite: t*log3 - t*log2 = t*log(3/2)
  have hlog :
      t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)
        =
      t * Real.log ((3 : ℝ) / (2 : ℝ)) := by
    have hpos3 : (0 : ℝ) < (3 : ℝ) := by norm_num
    have hpos2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hdiv :
        Real.log ((3 : ℝ) / (2 : ℝ)) = Real.log (3 : ℝ) - Real.log (2 : ℝ) := by
      -- log_div : log(a/b) = log a - log b
      simpa [div_eq_mul_inv] using (Real.log_div hpos3.ne' hpos2.ne')
    calc
      t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)
          = t * (Real.log (3 : ℝ) - Real.log (2 : ℝ)) := by ring
      _   = t * Real.log ((3 : ℝ) / (2 : ℝ)) := by
            simpa using congrArg (fun x => t * x) hdiv.symm

  -- factor and substitute
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
      ring
  _ =
      (pSigma σ (2 : ℝ) * pSigma σ (3 : ℝ)) *
        Real.sin (t * Real.log (3 : ℝ) - t * Real.log (2 : ℝ)) := by
      simp [hsin_sub]
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
  have hexp2 : pSigma σ (2 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (2 : ℝ)))
  have hexp3 : pSigma σ (3 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (3 : ℝ)))

  have hform := det23R_eq_pSigma_mul_sin_log_ratio (σ := σ) (t := t)

  intro hdet
  have : (pSigma σ (2 : ℝ)) * (pSigma σ (3 : ℝ)) *
            Real.sin (t * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
    simpa [hform] using hdet

  have hprod : (pSigma σ (2 : ℝ)) * (pSigma σ (3 : ℝ)) ≠ 0 :=
    mul_ne_zero hexp2 hexp3

  exact hsin ((mul_eq_zero.mp this).resolve_left hprod)

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
  -- cast det23R equality is definitional because all pieces are ℝ-valued
  have : ((det23R σ t : ℝ) : ℂ) = 0 := by
    simpa [det23R] using hC
  have : (det23R σ t : ℝ) = 0 := by
    exact_mod_cast this
  exact hR this

end W1

end XiPacket
end Targets
end Hyperlocal
