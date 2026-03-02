/-
  Hyperlocal/Targets/XiPacket/XiJetNonflatOfAnalytic.lean

  Axiom-free analytic discharge of jet-nonflatness for Xi at the anchor `sc s`.

  Snapshot-correct strategy (Mathlib snapshot you have):
  * `AnalyticAt` is `∃ p, HasFPowerSeriesAt ...`
  * If `p = 0`, then `Xi` is eventually zero near `z₀` (via `eventually_eq_zero`)
    and hence globally zero on `ℂ` by analytic identity (`eq_of_eventuallyEq`), contradicting `Xi 0 ≠ 0`.
  * If `p ≠ 0`, use `HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero` to produce a nonzero
    “derivative-ish” witness: an iterate of `dslope` evaluated at `z₀`.

  NOTE:
  This snapshot does NOT expose a usable `HasFPowerSeriesAt` ↔ `iteratedDeriv` bridge,
  so the correct theorem-level nonflatness witness is via `dslope`-iteration.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiNontrivial
import Hyperlocal.Targets.XiPacket.XiWindowDefs

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Topology

/-- `Xi` is analytic at every point (from `Xi_entire`). -/
private lemma Xi_analyticAt (z : ℂ) : AnalyticAt ℂ Xi z := by
  simpa [Xi] using (Xi_entire (z := z))

/-- `Xi` is analytic on `univ` (needed for the identity theorem `eq_of_eventuallyEq`). -/
private lemma Xi_analyticOnNhd_univ : AnalyticOnNhd ℂ Xi (Set.univ : Set ℂ) := by
  intro z hz
  simpa using Xi_analyticAt (z := z)

/--
Axiom-free nonflatness witness at the anchor, in the form supported by this snapshot:

`∃ m, ((Function.swap dslope z₀)^[m] Xi) z₀ ≠ 0`.
-/
theorem xiJetNonflat_dslope_exists (s : Hyperlocal.OffSeed Xi) :
    ∃ m : ℕ, ((Function.swap dslope (sc s))^[m] Xi) (sc s) ≠ 0 := by
  classical

  -- unpack analyticity at the anchor into a power series
  have hAna : AnalyticAt ℂ Xi (sc s) := Xi_analyticAt (z := sc s)
  rcases hAna with ⟨p, hp⟩

  -- show `p ≠ 0` (otherwise Xi is locally zero ⇒ globally zero ⇒ contradiction)
  have hp_ne : p ≠ 0 := by
    intro hp0
    have hp' : HasFPowerSeriesAt Xi (0 : FormalMultilinearSeries ℂ ℂ ℂ) (sc s) := by
      simpa [hp0] using hp
    have hev' : ∀ᶠ z in 𝓝 (sc s), Xi z = 0 :=
      HasFPowerSeriesAt.eventually_eq_zero (hf := hp')
    have hEv : Xi =ᶠ[𝓝 (sc s)] 0 := by
      simpa using hev'

    have hglobal : Xi = (fun _ : ℂ => 0) := by
      exact
        AnalyticOnNhd.eq_of_eventuallyEq
          (f := Xi) (g := fun _ : ℂ => 0)
          (hf := Xi_analyticOnNhd_univ)
          (hg := by
            intro z hz
            simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z))
          (z₀ := sc s) hEv

    -- contradiction from `Xi 0 ≠ 0`
    have h0 : Xi 0 = 0 := by
      simpa [hglobal]
    exact Xi_zero_ne_zero h0

  -- Now use Mathlib’s isolated-zeros API (method form in this snapshot):
  -- nonzero power series ⇒ the `p.order`-th dslope iterate at the point is nonzero.
  refine ⟨p.order, ?_⟩
  simpa using (hp.iterate_dslope_fslope_ne_zero hp_ne)

end XiPacket
end Targets
end Hyperlocal
