/-
  Hyperlocal/Targets/XiPacket/XiLocalFactor.lean

  Isolated “local analytic factor” lemma (axiom-free):

    xi a = 0  ⟹  ∃ J analytic at a,  xi z = (z - a) * J z

  Implementation strategy (snapshot-robust):
  Use `J := dslope xi a`. Then we have the *global* identity
    (z - a) • dslope xi a z = xi z - xi a
  (`sub_smul_dslope`), hence if `xi a = 0` we get
    xi z = (z - a) * dslope xi a z.
  Analyticity of `dslope` at `a` follows from the power-series API in
  `Mathlib.Analysis.Analytic.IsolatedZeros`:
    `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs

import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/--
LOCAL FACTOR (axiom-free).

This avoids brittle lemma-name drift by going through `dslope` + the power-series API.
-/
theorem xi_localFactor (a : ℂ) (ha : xi a = 0) :
    ∃ J : ℂ → ℂ, AnalyticAt ℂ J a ∧ (∀ z : ℂ, xi z = (z - a) * J z) := by
  classical

  -- `Xi_entire` is your Route-A “xi is entire” entrypoint.
  -- Unfolding `AnalyticAt` is fine: we will *use* the underlying power series.
  rcases (Xi_entire (z := a)) with ⟨p, hp⟩
  -- hp : HasFPowerSeriesAt xi p a

  -- `dslope` inherits a power series (hence analyticity) from `xi`.
  have hJ_an : AnalyticAt ℂ (dslope xi a) a := by
    refine ⟨p.fslope, ?_⟩
    simpa using (HasFPowerSeriesAt.has_fpower_series_dslope_fslope (f := xi) (p := p) (z₀ := a) hp)

  refine ⟨dslope xi a, hJ_an, ?_⟩
  intro z
  -- `sub_smul_dslope` is global: (z-a) • dslope f a z = f z - f a.
  -- Over `ℂ`, `•` is multiplication.
  have hz : (z - a) * dslope xi a z = xi z := by
    -- `simp [ha]` turns `xi z - xi a` into `xi z`.
    simpa [ha] using (sub_smul_dslope (f := xi) a z)
  exact hz.symm

end XiPacket
end Targets
end Hyperlocal
