/-
  Hyperlocal/Targets/XiPacket/XiRouteA_PivotNonflatLe2.lean

  Task D (Plan C++J): Stage–3 anchor robustness.

  Provide bounded nonflatness lemmas at the canonical anchors used by the quotient
  shift-bridge plumbing, phrased using `cderivIter` (snapshot-robust) rather than
  Mathlib's IteratedDeriv (missing in your snapshot).

  Targets:
    z_w0 : s.ρ
    z_wp2 : conj(s.ρ)
    z_wp3 : 1 - conj(s.ρ)
    z_wc  : 1 - s.ρ
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_NonflatLe2
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs  -- `cderivIter`
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace TAC

/-- Nonflatness (≤2) at the anchor `z = s.ρ`. -/
theorem routeA_nonflat_le2_z_w0 (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) (s.ρ) ≠ 0 := by
  simpa using (routeA_G_nonflat_le2 (s := s) (z := s.ρ))

/-- Nonflatness (≤2) at the anchor `z = conj(s.ρ)`. -/
theorem routeA_nonflat_le2_z_wp2 (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) ((starRingEnd ℂ) s.ρ) ≠ 0 := by
  simpa using (routeA_G_nonflat_le2 (s := s) (z := (starRingEnd ℂ) s.ρ))

/-- Nonflatness (≤2) at the anchor `z = 1 - conj(s.ρ)`. -/
theorem routeA_nonflat_le2_z_wp3 (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) (1 - (starRingEnd ℂ) s.ρ) ≠ 0 := by
  simpa using (routeA_G_nonflat_le2 (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)))

/-- Nonflatness (≤2) at the anchor `z = 1 - s.ρ` (useful for `wc`). -/
theorem routeA_nonflat_le2_z_wc (s : OffSeed Xi) :
    ∃ k : Fin 3, (cderivIter k.1 (routeA_G s)) (1 - s.ρ) ≠ 0 := by
  simpa using (routeA_G_nonflat_le2 (s := s) (z := (1 - s.ρ)))

end TAC
end XiPacket
end Targets
end Hyperlocal
