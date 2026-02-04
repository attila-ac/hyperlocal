/-
  Hyperlocal/Transport/PrimeTrigPacket.lean
-/

import Hyperlocal.Transport.PrimeSineRescue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport
namespace PrimeTrigPacket

open scoped Real

/-- p^{-σ} in the manuscript as exp(-σ log p). -/
def pSigma (σ : ℝ) (p : ℝ) : ℝ :=
  Real.exp (-σ * Real.log p)

/-- cosine coefficient: p^{-σ} cos(t log p). -/
def aCoeff (σ t : ℝ) (p : ℝ) : ℝ :=
  pSigma σ p * Real.cos (t * Real.log p)

/-- sine coefficient: p^{-σ} sin(t log p). -/
def bCoeff (σ t : ℝ) (p : ℝ) : ℝ :=
  pSigma σ p * Real.sin (t * Real.log p)

/--
Minimal “Stage-3 trig packet” at parameters (σ,t).
This is exactly what PrimeSineRescue consumes, but we store the linear combo
constraints *pointwise* to avoid typeclass inference getting stuck inside
the structure elaboration.
-/
structure Packet (σ t : ℝ) : Type where
  u0  : Fin 3 → ℝ
  uc  : Fin 3 → ℝ
  us  : Fin 3 → ℝ
  up2 : Fin 3 → ℝ
  up3 : Fin 3 → ℝ

  -- pointwise linear combo constraints (no `+`/`•` on function spaces here)
  hup2 :
    ∀ i : Fin 3,
      up2 i = u0 i
        + (aCoeff σ t (2 : ℝ)) * (uc i)
        + (bCoeff σ t (2 : ℝ)) * (us i)

  hup3 :
    ∀ i : Fin 3,
      up3 i = u0 i
        + (aCoeff σ t (3 : ℝ)) * (uc i)
        + (bCoeff σ t (3 : ℝ)) * (us i)

  hell2 : ell u0 uc up2 = 0
  hell3 : ell u0 uc up3 = 0
  hkappa : kappa u0 uc us ≠ 0

/-- Rebuild the vector-form equality needed by PrimeSineRescue (p=2). -/
lemma hup2_vec {σ t : ℝ} (P : Packet σ t) :
    P.up2 = P.u0 + (aCoeff σ t (2 : ℝ)) • P.uc + (bCoeff σ t (2 : ℝ)) • P.us := by
  funext i
  -- expand pointwise `+` and `•` on Pi-types, then close with `P.hup2 i`
  simpa [Pi.add_apply, Pi.smul_apply, add_assoc, mul_assoc] using (P.hup2 i)

/-- Rebuild the vector-form equality needed by PrimeSineRescue (p=3). -/
lemma hup3_vec {σ t : ℝ} (P : Packet σ t) :
    P.up3 = P.u0 + (aCoeff σ t (3 : ℝ)) • P.uc + (bCoeff σ t (3 : ℝ)) • P.us := by
  funext i
  simpa [Pi.add_apply, Pi.smul_apply, add_assoc, mul_assoc] using (P.hup3 i)

/--
Packet ⇒ phase-lock at primes 2 and 3 (and supplies κ ≠ 0).
-/
theorem offSeedPhaseLock_of_packet {σ t : ℝ} (P : Packet σ t) :
    ∃ κ : ℝ, κ ≠ 0 ∧
      Real.sin (t * Real.log (2 : ℝ)) = 0 ∧
      Real.sin (t * Real.log (3 : ℝ)) = 0 := by
  classical
  refine ⟨kappa P.u0 P.uc P.us, P.hkappa, ?_, ?_⟩

  · -- p = 2
    have hb2 : bCoeff σ t (2 : ℝ) = 0 := by
      exact coeff_eq_zero_of_ell_eq_zero
        (u0 := P.u0) (uc := P.uc) (us := P.us) (up := P.up2)
        (a := aCoeff σ t (2 : ℝ)) (b := bCoeff σ t (2 : ℝ))
        (hup := hup2_vec P) (hEll := P.hell2) (hk := P.hkappa)

    have hexp : pSigma σ (2 : ℝ) ≠ 0 := by
      simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (2 : ℝ)))

    have : pSigma σ (2 : ℝ) * Real.sin (t * Real.log (2 : ℝ)) = 0 := by
      simpa [bCoeff] using hb2

    exact (mul_eq_zero.mp this).resolve_left hexp

  · -- p = 3
    have hb3 : bCoeff σ t (3 : ℝ) = 0 := by
      exact coeff_eq_zero_of_ell_eq_zero
        (u0 := P.u0) (uc := P.uc) (us := P.us) (up := P.up3)
        (a := aCoeff σ t (3 : ℝ)) (b := bCoeff σ t (3 : ℝ))
        (hup := hup3_vec P) (hEll := P.hell3) (hk := P.hkappa)

    have hexp : pSigma σ (3 : ℝ) ≠ 0 := by
      simpa [pSigma] using (Real.exp_ne_zero (-σ * Real.log (3 : ℝ)))

    have : pSigma σ (3 : ℝ) * Real.sin (t * Real.log (3 : ℝ)) = 0 := by
      simpa [bCoeff] using hb3

    exact (mul_eq_zero.mp this).resolve_left hexp

end PrimeTrigPacket
end Transport
end Hyperlocal
