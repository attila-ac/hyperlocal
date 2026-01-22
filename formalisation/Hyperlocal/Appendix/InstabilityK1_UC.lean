/-
  Hyperlocal/Appendix/InstabilityK1_UC.lean

  k = 1: unit-circle elimination scaffold (compiles clean, no sorry).
  We keep it as a future upgrade path while proceeding with the seed plan.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Hyperlocal.Cancellation.InstabilityHyp

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1UC

open Complex

/-- Interface: the k=1 characteristic polynomial is a monic cubic
    with *real* coefficient functions of `t` and parameter `A`. -/
structure CoeffShapeK1 (A t : ℝ) : Type where
  b0 b1 b2 : ℝ
  -- keep a “monic” flag slot; fill with a real fact later
  monic : True := True.intro

/-- Evaluate the k=1 char poly at `z` from its coefficient package. -/
def P1_eval (A t : ℝ) (C : CoeffShapeK1 A t) (z : ℂ) : ℂ :=
  (1 : ℂ) * z^3 + (C.b2 : ℂ) * z^2 + (C.b1 : ℂ) * z + (C.b0 : ℂ)

/-- Real/imaginary parts on the unit circle: U,V are real-valued in θ. -/
def U (A t : ℝ) (C : CoeffShapeK1 A t) (θ : ℝ) : ℝ :=
  (P1_eval A t C (Complex.exp (θ * I))).re

def V (A t : ℝ) (C : CoeffShapeK1 A t) (θ : ℝ) : ℝ :=
  (P1_eval A t C (Complex.exp (θ * I))).im

/-- Elimination proxy on x = cos θ. -/
structure UCEliminationK1 (A t : ℝ) (C : CoeffShapeK1 A t) : Type where
  elim   : ℝ → ℝ
  sound  :
    ∀ θ : ℝ, elim (Real.cos θ) = 0 → (U A t C θ = 0 ∧ V A t C θ = 0)
  complete :
    ∀ θ : ℝ, (U A t C θ = 0 ∧ V A t C θ = 0) → elim (Real.cos θ) = 0

/-- If the elimination polynomial never vanishes on [-1,1], there are no
    unit-circle roots: P₁(e^{iθ}) ≠ 0 for all θ. -/
lemma no_unit_circle_root_k1
  {A t : ℝ} (C : CoeffShapeK1 A t)
  (E : UCEliminationK1 A t C)
  (hNZ : ∀ x : ℝ, (-1 ≤ x ∧ x ≤ 1) → E.elim x ≠ 0) :
  ∀ θ : ℝ, P1_eval A t C (Complex.exp (θ * I)) ≠ 0 := by
  intro θ h
  -- If P(e^{iθ}) = 0 then both real/imag parts vanish
  have hU0 : U A t C θ = 0 := by
    simpa [U] using congrArg Complex.re h
  have hV0 : V A t C θ = 0 := by
    simpa [V] using congrArg Complex.im h
  -- Elimination says elim(cos θ) = 0
  have hz : E.elim (Real.cos θ) = 0 := E.complete θ ⟨hU0, hV0⟩
  -- But cos θ ∈ [-1,1]
  have hc : (-1 ≤ Real.cos θ ∧ Real.cos θ ≤ 1) :=
    ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  -- Contradiction
  exact (hNZ (Real.cos θ) hc) hz

/-- A tiny success marker so this file stays “green” even when unused. -/
@[simp] lemma scaffold_ok : True := True.intro

end InstabilityK1UC
end Cancellation
end Hyperlocal
