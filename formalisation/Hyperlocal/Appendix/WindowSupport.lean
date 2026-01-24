/-
  Hyperlocal/Cancellation/WindowSupport.lean

  Window truncation helpers + “windowed pivot ⇒ QCC/TRC stencils” scaffold.

  This file is intentionally self-contained: it defines tiny local aliases
  (jetOfSeq, QCCStencilAt, TRCStencilAt) so you can drop in the real algebra
  later without fighting imports.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Polynomial.Basic

-- Bridge API for the windowed pivot recurrence
import Hyperlocal.Cancellation.Bridge
import Hyperlocal.Cancellation.BridgeAPI

-- QCC/TRC at (A₀,t₀) + Jet shape
import Hyperlocal.Cancellation.Setup
import Hyperlocal.Cancellation.Solo
import Hyperlocal.Cancellation.QCC
import Hyperlocal.Cancellation.TRC

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace WindowSupport

open Polynomial

/-- Coefficient sequence of a polynomial, by index. -/
def coeffSeq (p : Polynomial ℂ) : ℕ → ℂ := fun n => p.coeff n

/-- Leading coefficient is nonzero for a nonzero polynomial,
    rewritten as a statement about `coeffSeq` at `natDegree`. -/
lemma coeffSeq_natDegree_ne_zero
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    (coeffSeq p) p.natDegree ≠ 0 := by
  classical
  -- assume the coeff at natDegree is 0 and contradict `leadingCoeff_ne_zero`
  intro h
  have hcoeff : p.coeff p.natDegree = 0 := by
    simpa [coeffSeq] using h
  -- use the library lemma `coeff_natDegree : p.coeff p.natDegree = p.leadingCoeff`
  have hlead : p.leadingCoeff = 0 := by
    simpa [Polynomial.coeff_natDegree] using hcoeff
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hlead

/-- 6-jet cut-out from a coefficient sequence at base index `n0`. -/
def jetOfSeq (G : ℕ → ℂ) (n0 : ℕ) : Jet6 :=
  fun i => G (n0 + i.1)

/-- “QCC stencil holds for G at base index n0”. -/
def QCCStencilAt (G : ℕ → ℂ) (n0 : ℕ) : Prop :=
  QCCfun A₀ t₀ (jetOfSeq G n0) = 0

/-- “TRC stencil holds for G at base index n0”. -/
def TRCStencilAt (G : ℕ → ℂ) (n0 : ℕ) : Prop :=
  TRCfun A₀ t₀ (jetOfSeq G n0) = 0

/-- Placeholder for your “coefficient-shape at (A₀,t₀)” package.
    Replace the field(s) with concrete equalities later. -/
structure CoeffShapeAt (R : ℕ → ℂ) (A t : ℝ) : Prop where
  ok : True

/-- From a windowed pivot recurrence + coefficient-shape identifications
    at `(A₀,t₀)`, derive the QCC/TRC stencils at base index `n0`.

    TODO: Fill the proof once you wire the exact `R`-coefficient identities:
      * unfold `QCCfun` / `TRCfun` and `jetOfSeq`;
      * for the relevant coordinates, choose `m` and apply `wrec.recurrence m`;
      * use `hw : WindowUpTo R L` to kill out-of-window terms in the sums;
      * rewrite the remaining coefficients via `hIdent`.
-/
lemma stencils_from_window
  {R G H : ℕ → ℂ} {k L n0 : ℕ}
  (wrec   : BridgeAPI.WindowedPivotRecSpec R G H k L)
  (hw     : Bridge.WindowUpTo R L)
  (hIdent : CoeffShapeAt R A₀ t₀) :
  QCCStencilAt G n0 ∧ TRCStencilAt G n0 := by
  -- placeholder: replace with your concrete algebraic derivation
  admit

end WindowSupport
end Cancellation
end Hyperlocal
end section
