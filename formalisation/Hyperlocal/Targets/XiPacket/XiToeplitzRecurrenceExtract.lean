/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceExtract.lean

  ξ-specific Toeplitz/recurrence extraction frontier.

  Task 1 (Toeplitz extraction):
  Derive `XiToeplitzEllOut s` from a finite-window (Window 3) “row-stencil” recurrence
  hypothesis, using a pure linear-algebra elimination lemma (adjugate argument).

  NOTE (your line-89 “expected token”):
  In practice this is almost always triggered by a bad/unrecognized unicode token
  (most commonly `⬝`). This file uses plain `*` for matrix multiplication everywhere.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators Real
open Hyperlocal.Transport

/-- A length-3 “Toeplitz row” constraint on a real Window-3 vector. -/
def toeplitzRow3 (c v : Fin 3 → ℝ) : Prop :=
  (∑ i : Fin 3, c i * v i) = 0

/--
Minimal-model recurrence hypothesis (finite-window extraction form).

Interpretation:
for p=2 and p=3, there exists a nonzero Toeplitz row `c` annihilating
`reVec3(w0)`, `reVec3(wc)`, and the corresponding prime window `reVec3(wp)`.
-/
structure XiMinimalModelRecurrenceHyp (s : Hyperlocal.OffSeed Xi) : Prop where
  h2 :
    ∃ c2 : Fin 3 → ℝ,
      c2 ≠ 0 ∧
      toeplitzRow3 c2 (reVec3 (w0 s)) ∧
      toeplitzRow3 c2 (reVec3 (wc s)) ∧
      toeplitzRow3 c2 (reVec3 (wp2 s))
  h3 :
    ∃ c3 : Fin 3 → ℝ,
      c3 ≠ 0 ∧
      toeplitzRow3 c3 (reVec3 (w0 s)) ∧
      toeplitzRow3 c3 (reVec3 (wc s)) ∧
      toeplitzRow3 c3 (reVec3 (wp3 s))

/--
Semantic input (for now): ξ satisfies the minimal-model recurrence hypothesis.
This is the isolated “recurrence object” frontier; EllOut is derived from it.
-/
axiom xiMinimalModelRecurrenceHyp (s : Hyperlocal.OffSeed Xi) :
  XiMinimalModelRecurrenceHyp s

/-!
### Pure linear algebra: kernel vector ⇒ det = 0 (adjugate argument)

If `M.mulVec v = 0` with `v ≠ 0`, then `det M = 0`.
Proof: apply `adjugate` and use `adj M * M = det(M) • 1`.
-/
private lemma det_eq_zero_of_mulVec_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (v : n → ℝ) (hv : v ≠ 0)
    (hMv : M.mulVec v = 0) :
    Matrix.det M = 0 := by
  classical

  -- apply adjugate.mulVec to the kernel equation
  have h0 : (Matrix.adjugate M).mulVec (M.mulVec v) = 0 := by
    simpa [hMv] using congrArg (fun w => (Matrix.adjugate M).mulVec w) hMv

  -- rewrite as ((adj M) * M).mulVec v = 0
  have h1 : ((Matrix.adjugate M) * M).mulVec v = 0 := by
    simpa [Matrix.mulVec_mulVec] using h0

  -- use adjugate_mul: adj(M) * M = det(M) • 1
  have h2 : ((Matrix.det M) • (1 : Matrix n n ℝ)).mulVec v = 0 := by
    simpa [Matrix.adjugate_mul] using h1

  -- simplify: (det M) • v = 0
  have h3 : (Matrix.det M) • v = 0 := by
    simpa [Matrix.smul_mulVec_assoc, Matrix.one_mulVec] using h2

  -- extract an index where v is nonzero
  have hv' : ∃ i : n, v i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    exact h i

  rcases hv' with ⟨i, hi⟩

  -- evaluate pointwise: (det M) * v i = 0
  have : Matrix.det M * v i = 0 := by
    have := congrArg (fun f => f i) h3
    simpa [Pi.smul_apply] using this

  exact (mul_eq_zero.mp this).resolve_right hi

/--
If a nonzero Toeplitz row `c` annihilates the three columns `u0, uc, up`,
then `ell(u0,uc,up)=0` (equivalently, `det(colsMat u0 uc up)=0`).
-/
private lemma ell_eq_zero_of_toeplitzRow3
    (c u0 uc up : Fin 3 → ℝ)
    (hc : c ≠ 0)
    (h0 : toeplitzRow3 c u0)
    (h1 : toeplitzRow3 c uc)
    (h2 : toeplitzRow3 c up) :
    Transport.ell u0 uc up = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin 3) ℝ := Transport.colsMat u0 uc up

  have hker : M.transpose.mulVec c = 0 := by
    funext j
    fin_cases j
    · -- j = 0 : column u0
      -- (Mᵀ.mulVec c) 0 = ∑ i, M i 0 * c i = ∑ i, u0 i * c i
      -- commute to match toeplitzRow3: ∑ i, c i * u0 i = 0
      have : (∑ i : Fin 3, u0 i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using h0
      simpa [M, Transport.colsMat, Transport.baseMat, Matrix.mulVec, Matrix.transpose] using this
    · -- j = 1 : column uc
      have : (∑ i : Fin 3, uc i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using h1
      simpa [M, Transport.colsMat, Transport.baseMat, Matrix.mulVec, Matrix.transpose] using this
    · -- j = 2 : column up
      have : (∑ i : Fin 3, up i * c i) = 0 := by
        simpa [toeplitzRow3, mul_comm] using h2
      simpa [M, Transport.colsMat, Transport.baseMat, Matrix.mulVec, Matrix.transpose] using this

  have hdetT : Matrix.det M.transpose = 0 :=
    det_eq_zero_of_mulVec_eq_zero (M := M.transpose) (v := c) hc hker

  have hdet : Matrix.det M = 0 := by
    simpa [Matrix.det_transpose] using hdetT

  simpa [Transport.ell, M] using hdet

/-- Recurrence hypothesis ⇒ the two determinant “ell-out” constraints. -/
theorem xiToeplitzEllOut_of_minRecurrence
    (s : Hyperlocal.OffSeed Xi)
    (h : XiMinimalModelRecurrenceHyp s) :
    XiToeplitzEllOut s := by
  refine ⟨?_, ?_⟩
  · rcases h.h2 with ⟨c2, hc2, hc2_w0, hc2_wc, hc2_wp2⟩
    exact ell_eq_zero_of_toeplitzRow3
      c2
      (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s))
      hc2
      hc2_w0 hc2_wc hc2_wp2
  · rcases h.h3 with ⟨c3, hc3, hc3_w0, hc3_wc, hc3_wp3⟩
    exact ell_eq_zero_of_toeplitzRow3
      c3
      (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s))
      hc3
      hc3_w0 hc3_wc hc3_wp3

/--
Public endpoint (same name/type as before), now a theorem:

  minimal-model recurrence hypothesis
  ⇒ finite Toeplitz window constraint
  ⇒ XiToeplitzEllOut(s).
-/
theorem xiToeplitzEllOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiToeplitzEllOut s := by
  exact xiToeplitzEllOut_of_minRecurrence (s := s) (xiMinimalModelRecurrenceHyp (s := s))

end XiPacket
end Targets
end Hyperlocal
