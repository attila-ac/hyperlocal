/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaPivotNonzero.lean

  Minimal Prop-class gate for the identity route:

    XiKappaPivotNonzero s  :=  (∃m, kappaAt m s ≠ 0) ∨ (∃m, kappaAtIm m s ≠ 0)

  This is theorem-only and AXIOM-FREE: we install it from
  `exists_kappaAt_or_kappaAtIm_ne_zero`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAtSomeOrderNonzeroFromJetNonflat

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/-- Pivot gate: there exists some order where κ is nonzero, in re- or im-pivot form. -/
class XiKappaPivotNonzero (s : Hyperlocal.OffSeed Xi) : Prop where
  out : (∃ m : ℕ, kappaAt m s ≠ 0) ∨ (∃ m : ℕ, kappaAtIm m s ≠ 0)

/-- AXIOM-FREE instance from the jet-pivot nonvanishing theorem. -/
instance (s : Hyperlocal.OffSeed Xi) : XiKappaPivotNonzero s :=
  ⟨exists_kappaAt_or_kappaAtIm_ne_zero (s := s)⟩

@[simp] lemma xiKappaPivotNonzero_out (s : Hyperlocal.OffSeed Xi) [h : XiKappaPivotNonzero s] :
    (∃ m : ℕ, kappaAt m s ≠ 0) ∨ (∃ m : ℕ, kappaAtIm m s ≠ 0) :=
  h.out

end XiPacket
end Targets
end Hyperlocal
