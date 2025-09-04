import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Notation
import Hyperlocal.Cancellation.Solo      -- Jet6, diagScale, applyM, kernel_trivial
import Hyperlocal.Cancellation.Setup     -- A₀, t₀, diag_nonzero_at_rho'

noncomputable section
namespace Hyperlocal
namespace Cancellation

open Complex

/-
TRC as a near–diagonal functional operator on Jet6.
We keep the same diagonal weights `diagScale A t i`, but place the “bumps”
in the complementary slots to QCC:

  (Tx)₀ = d₀ x₀
  (Tx)₁ = (1-2A) x₀ + d₁ x₁
  (Tx)₂ = d₂ x₂
  (Tx)₃ = (2 i t) x₂ + d₃ x₃
  (Tx)₄ = d₄ x₄
  (Tx)₅ = d₅ x₅

where dᵢ = diagScale A t i,
      (2 i t) = (2 : ℂ)*I*(t : ℂ),
      (1-2A)  = (1 : ℂ) - (2 : ℂ)*(A : ℂ).
-/
def TRCfun (A t : ℝ) (x : Jet6) : Jet6 :=
  ![
    diagScale A t 0 * x 0,
    ((1 : ℂ) - (2 : ℂ) * (A : ℂ)) * x 0 + diagScale A t 1 * x 1,
    diagScale A t 2 * x 2,
    ((2 : ℂ) * I * (t : ℂ)) * x 2 + diagScale A t 3 * x 3,
    diagScale A t 4 * x 4,
    diagScale A t 5 * x 5
  ]

@[simp] lemma TRCfun_closed (A t : ℝ) (x : Jet6) :
  TRCfun A t x =
    ![
      diagScale A t 0 * x 0,
      ((1 : ℂ) - (2 : ℂ) * (A : ℂ)) * x 0 + diagScale A t 1 * x 1,
      diagScale A t 2 * x 2,
      ((2 : ℂ) * I * (t : ℂ)) * x 2 + diagScale A t 3 * x 3,
      diagScale A t 4 * x 4,
      diagScale A t 5 * x 5
    ] := rfl

/-- If all diagonal weights are nonzero, TRC has trivial kernel (same elimination pattern). -/
theorem kernel_TRC_trivial
    (A t : ℝ)
    (h : ∀ i : Fin 6, diagScale A t i ≠ 0)
    {x : Jet6} (hx : TRCfun A t x = 0) :
    x = 0 := by
  -- i = 0
  have h0 : diagScale A t 0 * x 0 = 0 := by
    have := congrArg (fun v => v 0) hx
    simpa [TRCfun_closed] using this
  have hx0 : x 0 = 0 := by
    rcases (mul_eq_zero.mp h0) with hdiag0 | hx0
    · exact (h 0 hdiag0).elim
    · exact hx0
  -- i = 1  (depends on x0)
  have h1 : ((1 : ℂ) - (2 : ℂ) * (A : ℂ)) * x 0 + diagScale A t 1 * x 1 = 0 := by
    have := congrArg (fun v => v 1) hx
    simpa [TRCfun_closed] using this
  have hx1 : x 1 = 0 := by
    have : diagScale A t 1 * x 1 = 0 := by simpa [hx0] using h1
    rcases (mul_eq_zero.mp this) with hdiag1 | hx1
    · exact (h 1 hdiag1).elim
    · exact hx1
  -- i = 2
  have h2 : diagScale A t 2 * x 2 = 0 := by
    have := congrArg (fun v => v 2) hx
    simpa [TRCfun_closed] using this
  have hx2 : x 2 = 0 := by
    rcases (mul_eq_zero.mp h2) with hdiag2 | hx2
    · exact (h 2 hdiag2).elim
    · exact hx2
  -- i = 3  (depends on x2)
  have h3 : ((2 : ℂ) * I * (t : ℂ)) * x 2 + diagScale A t 3 * x 3 = 0 := by
    have := congrArg (fun v => v 3) hx
    simpa [TRCfun_closed] using this
  have hx3 : x 3 = 0 := by
    have : diagScale A t 3 * x 3 = 0 := by simpa [hx2] using h3
    rcases (mul_eq_zero.mp this) with hdiag3 | hx3
    · exact (h 3 hdiag3).elim
    · exact hx3
  -- i = 4
  have h4 : diagScale A t 4 * x 4 = 0 := by
    have := congrArg (fun v => v 4) hx
    simpa [TRCfun_closed] using this
  have hx4 : x 4 = 0 := by
    rcases (mul_eq_zero.mp h4) with hdiag4 | hx4
    · exact (h 4 hdiag4).elim
    · exact hx4
  -- i = 5
  have h5 : diagScale A t 5 * x 5 = 0 := by
    have := congrArg (fun v => v 5) hx
    simpa [TRCfun_closed] using this
  have hx5 : x 5 = 0 := by
    rcases (mul_eq_zero.mp h5) with hdiag5 | hx5
    · exact (h 5 hdiag5).elim
    · exact hx5
  -- done
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3, hx4, hx5]

/-- Specialization at `(A₀,t₀)=(-1/2,1)`. -/
theorem kernel_TRC_trivial_at_rho'
    {x : Jet6} (hx : TRCfun A₀ t₀ x = 0) : x = 0 :=
  kernel_TRC_trivial A₀ t₀ diag_nonzero_at_rho' hx

@[simp] lemma TRCfun_zero (A t : ℝ) : TRCfun A t (fun _ => (0 : ℂ)) = 0 := by
  funext i
  fin_cases i <;> simp [TRCfun_closed]


end Cancellation
end Hyperlocal
