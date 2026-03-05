/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_RouteA_NonflatLe2_Landing.lean

  Front~NF landing surface (Route–A bounded nonflatness ≤ 2).

  Design:
  - We do *not* attempt to manufacture nonvanishing from `FactorisedByQuartet`,
    because in this repo that interface is only multiplicative (`H = R * G`) and
    does not encode cofactor nonvanishing.
  - Instead, we state the correct semantic seam as a small provider class:
      one nonzero coordinate of `jet3 (routeA_G s) z` at each canonical anchor z.
  - Given that input, bounded nonflatness ≤ 2 is immediate (take k = 0/1/2).

  Policy:
  - Downstream should import the *ax surface* file which re-exports these names.
  - The provider instance belongs in your analytic / pivot pipeline track.
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

/-
  We reuse the `jet3` definition from
  `XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets.lean`
  (it is in namespace `...XiPacket.TAC` there as well), so we do not re-declare it.
-/

/-- Semantic provider: a nonzero jet3 coordinate at each canonical Route–A anchor. -/
class RouteA_Jet3NonzeroAnchors : Prop where
  nonzero_at_rho :
    ∀ s : OffSeed Xi, ∃ i : Fin 3, (jet3 (routeA_G s) (s.ρ)) i ≠ 0
  nonzero_at_conj_rho :
    ∀ s : OffSeed Xi, ∃ i : Fin 3, (jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)) i ≠ 0
  nonzero_at_one_sub_conj_rho :
    ∀ s : OffSeed Xi, ∃ i : Fin 3,
      (jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)) i ≠ 0
  nonzero_at_one_sub_rho :
    ∀ s : OffSeed Xi, ∃ i : Fin 3, (jet3 (routeA_G s) (1 - s.ρ)) i ≠ 0

/--
Core deterministic lemma:

If some coordinate of `jet3 f z` is nonzero, then `f` is not flat up to order 2 at `z`,
in the repo’s preferred form `∃ k : Fin 3, iteratedDeriv k f z ≠ 0`.

Snapshot-robust: we expand `iteratedDeriv` by `iteratedDeriv_succ` under `fin_cases`.
-/
lemma nonflat_le2_of_jet3_coord_ne_zero (f : ℂ → ℂ) (z : ℂ) :
    (∃ i : Fin 3, (jet3 f z) i ≠ 0) →
      ∃ k : Fin 3, (iteratedDeriv k.1 f) z ≠ 0 := by
  intro h
  rcases h with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  -- Expand the chosen coordinate i ∈ {0,1,2}.
  -- The key is to unfold iteratedDeriv by `iteratedDeriv_succ` as well,
  -- so that k=2 becomes `deriv (deriv f) z`.
  fin_cases i <;>
    (simp [jet3, iteratedDeriv_succ] at hi ⊢ <;> exact hi)

/-- Bounded nonflatness (≤2) at the anchor `ρ`. -/
theorem routeA_G_nonflat_le2_at_rho_iterated
    [RouteA_Jet3NonzeroAnchors] (s : OffSeed Xi) :
    ∃ k : Fin 3, (iteratedDeriv k.1 (routeA_G s)) s.ρ ≠ 0 := by
  exact nonflat_le2_of_jet3_coord_ne_zero (f := routeA_G s) (z := s.ρ)
    (RouteA_Jet3NonzeroAnchors.nonzero_at_rho (s := s))

/-- Bounded nonflatness (≤2) at the anchor `conj ρ`. -/
theorem routeA_G_nonflat_le2_at_conj_rho_iterated
    [RouteA_Jet3NonzeroAnchors] (s : OffSeed Xi) :
    ∃ k : Fin 3,
      (iteratedDeriv k.1 (routeA_G s)) ((starRingEnd ℂ) s.ρ) ≠ 0 := by
  exact nonflat_le2_of_jet3_coord_ne_zero (f := routeA_G s) (z := (starRingEnd ℂ) s.ρ)
    (RouteA_Jet3NonzeroAnchors.nonzero_at_conj_rho (s := s))

/-- Bounded nonflatness (≤2) at the anchor `1 - conj ρ`. -/
theorem routeA_G_nonflat_le2_at_one_sub_conj_rho_iterated
    [RouteA_Jet3NonzeroAnchors] (s : OffSeed Xi) :
    ∃ k : Fin 3,
      (iteratedDeriv k.1 (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) ≠ 0 := by
  exact nonflat_le2_of_jet3_coord_ne_zero (f := routeA_G s) (z := 1 - (starRingEnd ℂ) s.ρ)
    (RouteA_Jet3NonzeroAnchors.nonzero_at_one_sub_conj_rho (s := s))

/-- Bounded nonflatness (≤2) at the anchor `1 - ρ`. -/
theorem routeA_G_nonflat_le2_at_one_sub_rho_iterated
    [RouteA_Jet3NonzeroAnchors] (s : OffSeed Xi) :
    ∃ k : Fin 3, (iteratedDeriv k.1 (routeA_G s)) (1 - s.ρ) ≠ 0 := by
  exact nonflat_le2_of_jet3_coord_ne_zero (f := routeA_G s) (z := 1 - s.ρ)
    (RouteA_Jet3NonzeroAnchors.nonzero_at_one_sub_rho (s := s))

end TAC

end XiPacket
end Targets
end Hyperlocal
