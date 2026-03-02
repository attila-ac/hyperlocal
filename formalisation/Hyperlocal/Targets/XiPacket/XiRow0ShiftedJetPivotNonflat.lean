/-
  Hyperlocal/Targets/XiPacket/XiRow0ShiftedJetPivotNonflat.lean

  AXIOM-FREE:

  Provided exports:
    • `xiShiftedKappaRe_or_im_exists_ne0` : (∃k, Re≠0) ∨ (∃k, Im≠0)
    • `xiShiftedJet_exists_ne0`           : ∃k, cderivIter k Xi (sc s) ≠ 0
-/

import Hyperlocal.Targets.XiPacket.XiRow0ShiftedJetPivot
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real

/-- Existence of a shifted κ diagnostic witness, in Re/Im split form (AXIOM-FREE). -/
theorem xiShiftedKappaRe_or_im_exists_ne0 (s : OffSeed Xi) :
    (∃ k : ℕ, xiShiftedKappaRe k s ≠ 0)
    ∨ (∃ k : ℕ, ((cderivIter k Xi (sc s))).im ≠ 0) := by
  -- This is exactly `xiJetNonflat_re_or_im` rewritten into the shifted names.
  simpa [xiShiftedKappaRe] using
    (_root_.Hyperlocal.Targets.XiPacket.xiJetNonflat_re_or_im (s := s))

/-- Existence of a nonzero shifted jet entry (complex, some order). -/
theorem xiShiftedJet_exists_ne0 (s : OffSeed Xi) :
    ∃ k : ℕ, (cderivIter k Xi (sc s)) ≠ (0 : ℂ) := by
  have h := _root_.Hyperlocal.Targets.XiPacket.xiJetNonflat_re_or_im (s := s)
  cases h with
  | inl hRe =>
      rcases hRe with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro hz
      have : (cderivIter k Xi (sc s)).re = 0 := by simpa [hz]
      exact hk this
  | inr hIm =>
      rcases hIm with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro hz
      have : (cderivIter k Xi (sc s)).im = 0 := by simpa [hz]
      exact hk this

end XiPacket
end Targets
end Hyperlocal
