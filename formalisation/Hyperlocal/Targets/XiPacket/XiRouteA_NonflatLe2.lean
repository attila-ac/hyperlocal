/-
  Hyperlocal/Targets/XiPacket/XiRouteA_NonflatLe2.lean

  Task D (Plan C++J): bounded nonflatness statement for Route–A witness `routeA_G s`.

  REFACTOR (2026-03-01):
  * Keep project-facing statements in terms of `cderivIter` (snapshot-robust).
  * Shrink the *axiom surface* to the ONLY anchors actually consumed downstream:
        z = ρ,  conj ρ,  1 - conj ρ,  1 - ρ
    (see `XiRouteA_PivotNonflatLe2.lean`).

  Status:
  * Still AXIOMATIC at these four anchors until we wire the manuscript proof.
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.TACAnalytic_CDerivIterBridge
import Hyperlocal.Targets.XiPacket.TACAnalytic_RouteA_NonflatLe2_AxiomSurface
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-! ## Anchor points actually used downstream -/

namespace TAC

/-- The four canonical Route–A anchors (the only ones we care about right now). -/
def isRouteAAnchor (s : OffSeed Xi) (z : ℂ) : Prop :=
  z = s.ρ
  ∨ z = (starRingEnd ℂ) s.ρ
  ∨ z = (1 : ℂ) - (starRingEnd ℂ) s.ρ
  ∨ z = (1 : ℂ) - s.ρ

/-!
The remaining analytic cliff is isolated in
`TACAnalytic_RouteA_NonflatLe2_AxiomSurface.lean`.

This file is intentionally **axiom-free**: it only converts the axiom-surface
`iteratedDeriv` statements into the project-facing `cderivIter` API.
-/

/-- Pointwise bridge `cderivIter = iteratedDeriv` (no simp loops). -/
private lemma cderivIter_eq_iteratedDeriv_apply
    (m : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    (cderivIter m f) z = (iteratedDeriv m f) z := by
  simpa using (TAC.cderivIter_apply (m := m) (f := f) (z := z))

/--
Project-facing bounded nonflatness (≤2) at the canonical anchors, in terms of `cderivIter`.
-/
theorem routeA_G_nonflat_le2_at_rho (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) s.ρ ≠ 0 := by
  rcases TAC.routeA_G_nonflat_le2_at_rho_iterated (s := s) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hbridge :=
    cderivIter_eq_iteratedDeriv_apply (m := k.1) (f := routeA_G s) (z := s.ρ)
  exact (by simpa [hbridge] using hk)

theorem routeA_G_nonflat_le2_at_conj_rho (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) ((starRingEnd ℂ) s.ρ) ≠ 0 := by
  rcases TAC.routeA_G_nonflat_le2_at_conj_rho_iterated (s := s) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hbridge :=
    cderivIter_eq_iteratedDeriv_apply (m := k.1) (f := routeA_G s) (z := (starRingEnd ℂ) s.ρ)
  exact (by simpa [hbridge] using hk)

theorem routeA_G_nonflat_le2_at_one_sub_conj_rho (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) ((1 : ℂ) - (starRingEnd ℂ) s.ρ) ≠ 0 := by
  rcases TAC.routeA_G_nonflat_le2_at_one_sub_conj_rho_iterated (s := s) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hbridge :=
    cderivIter_eq_iteratedDeriv_apply (m := k.1) (f := routeA_G s)
      (z := (1 : ℂ) - (starRingEnd ℂ) s.ρ)
  exact (by simpa [hbridge] using hk)

theorem routeA_G_nonflat_le2_at_one_sub_rho (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) ((1 : ℂ) - s.ρ) ≠ 0 := by
  rcases TAC.routeA_G_nonflat_le2_at_one_sub_rho_iterated (s := s) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hbridge :=
    cderivIter_eq_iteratedDeriv_apply (m := k.1) (f := routeA_G s) (z := (1 : ℂ) - s.ρ)
  exact (by simpa [hbridge] using hk)

/--
Compatibility helper: nonflatness (≤2) at a `z` provided you prove `z` is one of the
four canonical anchors.
-/
theorem routeA_G_nonflat_le2_of_isRouteAAnchor
    (s : OffSeed Xi) (z : ℂ) (hz : isRouteAAnchor s z) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) z ≠ 0 := by
  rcases hz with hzρ | hzconj | hzoneconj | hzoneρ
  · subst hzρ
    simpa using routeA_G_nonflat_le2_at_rho (s := s)
  · subst hzconj
    simpa using routeA_G_nonflat_le2_at_conj_rho (s := s)
  · subst hzoneconj
    simpa using routeA_G_nonflat_le2_at_one_sub_conj_rho (s := s)
  · subst hzoneρ
    simpa using routeA_G_nonflat_le2_at_one_sub_rho (s := s)

end TAC

end XiPacket
end Targets
end Hyperlocal
