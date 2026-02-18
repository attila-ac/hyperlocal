/-
  Hyperlocal/Targets/XiPacket/XiJetNonflatOfAnalytic.lean

  Route-B analytic insertion point (acyclic):
  Jet nonflatness at the anchor `sc s` for `s : OffSeed Xi`.

  This replaces the earlier hard zeta-specific nonvanishing axiom at `Λ(sc s)`.

  Once the analytic theory is formalised, replace this axiom by a theorem.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Route-B semantic cliff (temporary):
there exists some order `m` such that the **real part** of the `m`-th complex
derivative of `Xi` at `sc s` is nonzero.
-/
axiom xiJetNonflat_re_exists (s : Hyperlocal.OffSeed Xi) :
  ∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0

/-- Backward-compatible derived form: some complex derivative is nonzero. -/
theorem xiJetNonflat_exists (s : Hyperlocal.OffSeed Xi) :
  ∃ m : ℕ, (cderivIter m Xi) (sc s) ≠ 0 := by
  rcases xiJetNonflat_re_exists (s := s) with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro hz
  exact hm (by simpa [hz])

end XiPacket
end Targets
end Hyperlocal
