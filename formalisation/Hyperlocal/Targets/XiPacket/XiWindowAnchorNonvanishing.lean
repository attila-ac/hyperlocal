/-
  Hyperlocal/Targets/XiPacket/XiAnchorNonvanishing.lean

  Minimal Prop-class capturing the single anchor nonvanishing obligation used by
  the Toeplitz/κ pipeline.

  This file is theorem-only: it contains no legacy axioms.
  It also re-exports the jet-nonflatness split lemma `xiJetNonflat_re_or_im`,
  because downstream payload constructors use that name as a stable interface.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiJetNonflatOfAnalytic
import Hyperlocal.Targets.XiPacket.XiDslopeToKappaAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Anchor nonvanishing: real part of `Xi` at the seed anchor is nonzero. -/
class XiAnchorNonvanishing (s : Hyperlocal.OffSeed Xi) : Prop where
  xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0

/-! ## Jet-nonflatness at the anchor (AXIOM-FREE)

Downstream still expects the semantic interface lemma:

`xiJetNonflat_re_or_im : ...`

We derive it axiom-free from `xiJetNonflat_dslope_exists`
using dslope→cderivIter helper lemmas in `XiDslopeToKappaAtOrder.lean`.
-/

/-- Semantic nonflatness at the anchor: some complex derivative is nonzero. -/
def XiJetNonflat (s : Hyperlocal.OffSeed Xi) : Prop :=
  ∃ m : ℕ, (cderivIter m Xi) (sc s) ≠ 0

/-- Nonflatness at the anchor (AXIOM-FREE): derived from `xiJetNonflat_dslope_exists`. -/
theorem xiJetNonflat (s : Hyperlocal.OffSeed Xi) : XiJetNonflat s := by
  rcases xiJetNonflat_dslope_exists (s := s) with ⟨m, hmDs⟩
  refine ⟨m, ?_⟩
  exact cderivIter_ne0_of_dslopeIter_ne0 (m := m) (s := s) hmDs

/-- Re/Im split form used by payload constructors (AXIOM-FREE). -/
theorem xiJetNonflat_re_or_im (s : Hyperlocal.OffSeed Xi) :
    (∃ m : ℕ, (((cderivIter m Xi) (sc s))).re ≠ 0) ∨
    (∃ m : ℕ, (((cderivIter m Xi) (sc s))).im ≠ 0) := by
  rcases xiJetNonflat_dslope_exists (s := s) with ⟨m, hmDs⟩
  have hparts :
      (((cderivIter m Xi) (sc s))).re ≠ 0 ∨
      (((cderivIter m Xi) (sc s))).im ≠ 0 :=
    cderivIter_re_ne0_or_im_ne0_of_dslopeIter_ne0 (m := m) (s := s) hmDs
  cases hparts with
  | inl hre =>
      exact Or.inl ⟨m, hre⟩
  | inr him =>
      exact Or.inr ⟨m, him⟩

end XiPacket
end Targets
end Hyperlocal
