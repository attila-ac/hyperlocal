/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_XiTransportCompat.lean

  Cycle-safe compatibility lemma between:

    * finite matrix transport `TAC.transportMat` (from TACTransportTruncated)
    * concrete transport operator `XiTransportOp` (Toeplitz-right shift stencil)

  IMPORTANT:
  In this repo, `XiTransportOp` is lower-triangular in Window coordinates, so it
  corresponds to the TRANSPOSE of the manuscript-style upper-triangular matrix.

  Result (N=3, n=2):
    XiTransportOp 2 s  =  (TAC.transportMat 3 (delta s)).transpose.mulVec
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated
import Hyperlocal.Targets.XiTransportConvolution
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC

open scoped BigOperators
open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Lower-triangular (transpose) variant of the finite transport:
    `transportLower N δ Γ = (transportMat N δ).transpose.mulVec Γ`. -/
def transportLower (N : ℕ) (δ : ℂ) (Γ : Fin N → ℂ) : Fin N → ℂ :=
  (transportMat N δ).transpose.mulVec Γ

@[simp] lemma transportLower_def (N : ℕ) (δ : ℂ) (Γ : Fin N → ℂ) :
    transportLower N δ Γ = (transportMat N δ).transpose.mulVec Γ := rfl

/-- Expand a sum over `Fin 3` into three terms. -/
private lemma sum_fin3 {α : Type} [AddCommMonoid α] (f : Fin 3 → α) :
    (∑ j : Fin 3, f j) = f 0 + f 1 + f 2 := by
  classical
  have h1 : (∑ j : Fin 3, f j) = f 0 + ∑ j : Fin 2, f j.succ := by
    simpa using (Fin.sum_univ_succ (n := 2) f)
  have h2 : (∑ j : Fin 2, f j.succ) = f 1 + f 2 := by
    let g : Fin 2 → α := fun j => f j.succ
    simpa [g] using (Fin.sum_univ_succ (n := 1) g)
  simpa [h2, add_assoc] using h1

namespace Compat3

open Hyperlocal.Targets.XiTransport

/-- Coefficient function used by `XiTransportOp`. -/
private def a (δr : ℝ) : ℕ → ℂ := XiTransport.shiftCoeff δr

/-- Cast δr to ℂ (for transportMat). -/
private def δc (δr : ℝ) : ℂ := (δr : ℂ)

/-- A `mulVec` expansion that avoids `Matrix.dotProduct` (works in older snapshots). -/
private lemma mulVec_eq_sum {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (v : n → ℂ) (i : n) :
    M.mulVec v i = ∑ j : n, M i j * v j := by
  rfl

/-- Compute `transportLower` at index 0. -/
lemma transportLower_fin0 (δr : ℝ) (w : Window 3) :
    transportLower 3 (δc δr) w (0 : Fin 3) = a δr 0 * w 0 := by
  classical
  -- unfold to an explicit Fin 3 sum
  unfold transportLower
  simp [mulVec_eq_sum, Matrix.transpose, sum_fin3, TAC.transportMat, a, δc, XiTransport.shiftCoeff]

/-- Compute `transportLower` at index 1. -/
lemma transportLower_fin1 (δr : ℝ) (w : Window 3) :
    transportLower 3 (δc δr) w (1 : Fin 3) = a δr 0 * w 1 + a δr 1 * w 0 := by
  classical
  unfold transportLower
  -- explicit sum over Fin 3, then simp the `if`s in `transportMat`
  simp [mulVec_eq_sum, Matrix.transpose, sum_fin3, TAC.transportMat, a, δc, XiTransport.shiftCoeff,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Compute `transportLower` at index 2. -/
lemma transportLower_fin2 (δr : ℝ) (w : Window 3) :
    transportLower 3 (δc δr) w (2 : Fin 3)
      = a δr 0 * w 2 + a δr 1 * w 1 + a δr 2 * w 0 := by
  classical
  unfold transportLower
  simp [mulVec_eq_sum, Matrix.transpose, sum_fin3, TAC.transportMat, a, δc, XiTransport.shiftCoeff,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Identify `transportLower` with `convCoeff` against `winSeqStd` on all indices. -/
theorem transportLower_apply_eq_convCoeff
    (δr : ℝ) (w : Window 3) (i : Fin 3) :
    transportLower 3 (δc δr) w i = convCoeff (a δr) (winSeqStd w) (i : ℕ) := by
  classical
  fin_cases i
  · simpa [transportLower_fin0, a] using
      (convCoeff_winSeqStd_zero (a := a δr) (w := w))
  · simpa [transportLower_fin1, a] using
      (convCoeff_winSeqStd_one (a := a δr) (w := w))
  · simpa [transportLower_fin2, a] using
      (convCoeff_winSeqStd_two (a := a δr) (w := w))

end Compat3

open Hyperlocal.Targets.XiTransport
open Compat3

/--
Main compatibility theorem:

For `n=2` (windows of length 3), the concrete operator `XiTransportOp 2 s`
equals the transpose-matrix transport `transportLower 3 (delta s)`.
-/
theorem XiTransportOp₂_eq_transportLower
    (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w
      =
    (fun i => transportLower 3 ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ) w i) := by
  classical
  funext i

  -- your lemma returns an equality of functions
  have hconv_fun :=
    Hyperlocal.Targets.XiTransport.XiTransportOp₂_apply_eq_convCoeff (s := s) (w := w)

  -- evaluate at i
  have hconv :
      (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w i =
        convCoeff (XiTransport.shiftCoeff (Hyperlocal.Targets.XiTransport.delta s))
          (winSeqStd w) (i : ℕ) := by
    simpa using congrArg (fun f => f i) hconv_fun

  have hrhs :
      transportLower 3 ((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ) w i
        =
      convCoeff (XiTransport.shiftCoeff (Hyperlocal.Targets.XiTransport.delta s))
        (winSeqStd w) (i : ℕ) := by
    simpa [Compat3.δc, Compat3.a] using
      (transportLower_apply_eq_convCoeff
        (δr := Hyperlocal.Targets.XiTransport.delta s) (w := w) (i := i))

  simpa [hrhs] using hconv

end TAC

end XiPacket
end Targets
end Hyperlocal
