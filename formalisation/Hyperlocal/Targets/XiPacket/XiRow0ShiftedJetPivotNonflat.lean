/-
  Hyperlocal/Targets/XiPacket/XiRow0ShiftedJetPivotNonflat.lean

  COMPLETE REPLACEMENT (fixes your errors):

  Key correction:
  * `xiJetNonflat_re_or_im` is an *existential over m*, not a k=0 statement.
  * Therefore, we provide theorem-level **existence** lemmas (the shapes you can actually
    discharge from the current Route-B nonflatness API).

  Provided exports:
    • `xiShiftedKappaRe_exists_ne0` : ∃ k, xiShiftedKappaRe k s ≠ 0
    • `xiShiftedJet_exists_ne0`     : ∃ k, cderivIter k Xi (sc s) ≠ 0
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

/-- Existence of a shifted κ-re witness, in the shifted-jet language. -/
theorem xiShiftedKappaRe_exists_ne0 (s : OffSeed Xi) :
    ∃ k : ℕ, xiShiftedKappaRe k s ≠ 0 := by
  -- This lemma already exists in your repo (used elsewhere): take it and rewrite.
  rcases (_root_.Hyperlocal.Targets.XiPacket.xiJetNonflat_re_exists (s := s)) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [xiShiftedKappaRe] using hk

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
