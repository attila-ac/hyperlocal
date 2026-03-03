/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaAtSomeOrderNonzeroFromJetNonflat.lean

  Theorem-level nonvanishing seam (AXIOM-FREE):

    from `xiJetNonflat_re_or_im` at the anchor,
    we get existence of an order `m` where either:
      kappaAt m s   ≠ 0   (real pivot), or
      kappaAtIm m s ≠ 0   (imag pivot).

  This is the correct “finish the nonvanishing work” endpoint:
  it replaces the *false target* “kappaAt0 ≠ 0 must hold” with the
  jet-pivot alternative that works for arbitrary multiplicity and avoids SZC.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing      -- now provides xiJetNonflat_re_or_im
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder   -- κ closed forms
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/--
Main theorem (AXIOM-FREE):
there exists some order `m` where κ is nonzero,
either in the real-pivot or imag-pivot incarnation.
-/
theorem exists_kappaAt_or_kappaAtIm_ne_zero (s : Hyperlocal.OffSeed Xi) :
    (∃ m : ℕ, kappaAt m s ≠ 0) ∨ (∃ m : ℕ, kappaAtIm m s ≠ 0) := by
  rcases xiJetNonflat_re_or_im (s := s) with hre | him
  ·
    rcases hre with ⟨m, hmre⟩
    have hk : kappaAt m s = ((cderivIter m Xi) (sc s)).re := by
      simpa [kappaAt] using (XiLemmaC_kappa_closedFormAt (m := m) (s := s))
    refine Or.inl ⟨m, ?_⟩
    exact hk.symm ▸ hmre
  ·
    rcases him with ⟨m, hmim⟩
    have hk : kappaAtIm m s = ((cderivIter m Xi) (sc s)).im := by
      simpa [kappaAtIm] using (XiLemmaC_kappa_closedFormAt_im (m := m) (s := s))
    refine Or.inr ⟨m, ?_⟩
    exact hk.symm ▸ hmim

end XiPacket
end Targets
end Hyperlocal
