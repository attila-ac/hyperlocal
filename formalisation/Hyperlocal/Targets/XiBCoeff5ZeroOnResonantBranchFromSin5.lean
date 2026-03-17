import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Targets.XiPacket
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
Exact local equivalence at prime 5, forward direction:

`sin(t log 5) = 0` on the exact resonant branch implies `bCoeff(σ,t,5)=0`.
-/
theorem bCoeff5_zero_on_resonant_branch_of_sin5
    (h5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (5 : ℝ)) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      bCoeff (σ s) (t s) (5 : ℝ) = 0 := by
  intro s hres
  rw [bCoeff]
  simp [h5_res s hres]

/--
Exact local equivalence at prime 5, reverse direction:

`bCoeff(σ,t,5)=0` on the exact resonant branch implies `sin(t log 5)=0`.
-/
theorem sin5_zero_on_resonant_branch_of_bCoeff5
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (5 : ℝ)) = 0 := by
  intro s hres
  have hb : pSigma (σ s) (5 : ℝ) * Real.sin ((t s) * Real.log (5 : ℝ)) = 0 := by
    simpa [bCoeff] using hb5_res s hres
  have hp : pSigma (σ s) (5 : ℝ) ≠ 0 := by
    simpa [pSigma] using (Real.exp_ne_zero (-(σ s) * Real.log (5 : ℝ)))
  exact (mul_eq_zero.mp hb).resolve_left hp

/--
Prime-5 local equivalence on the resonant branch.
-/
theorem sin5_zero_on_resonant_branch_iff_bCoeff5_zero
    (s : Hyperlocal.OffSeed Xi)
    (hres : Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0) :
    Real.sin ((t s) * Real.log (5 : ℝ)) = 0 ↔
      bCoeff (σ s) (t s) (5 : ℝ) = 0 := by
  constructor
  · intro h5
    rw [bCoeff]
    simp [h5]
  · intro hb5
    have hb : pSigma (σ s) (5 : ℝ) * Real.sin ((t s) * Real.log (5 : ℝ)) = 0 := by
      simpa [bCoeff] using hb5
    have hp : pSigma (σ s) (5 : ℝ) ≠ 0 := by
      simpa [pSigma] using (Real.exp_ne_zero (-(σ s) * Real.log (5 : ℝ)))
    exact (mul_eq_zero.mp hb).resolve_left hp

end Targets
end Hyperlocal
