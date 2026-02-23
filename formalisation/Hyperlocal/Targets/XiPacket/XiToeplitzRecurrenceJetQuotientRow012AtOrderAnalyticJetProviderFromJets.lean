/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets.lean

  Step 4.5 (bridge): derive the window=canonical-jet equalities from *jet facts*.

  Motivation:
    The remaining analytic cliff was refactored into the explicit typeclass
      [TAC.XiJetWindowEqAtOrderProvider].

    In practice, it is often easier to prove jet predicates
      IsJet3AtOrder m z (w?At m s)
    than to prove raw window equalities. This file provides the deterministic
    conversion:

      IsJet3AtOrder m z w  ⇒  w = xiJet3AtOrder m z

    and then packages the three equalities into `XiJetWindowEqAtOrder m s`.

  This file contains NO axioms.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

/-- Deterministic ext lemma: two Jet3 windows for the same function at the same point are equal. -/
theorem window_eq_of_isJet3At
    {F : ℂ → ℂ} {z : ℂ} {w₁ w₂ : Window 3}
    (H₁ : IsJet3At F z w₁) (H₂ : IsJet3At F z w₂) :
    w₁ = w₂ := by
  classical
  ext i
  fin_cases i <;> rcases H₁ with ⟨h10, h11, h12⟩ <;> rcases H₂ with ⟨h20, h21, h22⟩ <;> simp_all

/--
Canonicalization lemma (order-m):

If `w` is an order-m jet of `Xi` at `z`, then it equals the canonical jet window
`xiJet3AtOrder m z`.
-/
theorem window_eq_xiJet3AtOrder_of_isJet3AtOrder
    (m : ℕ) (z : ℂ) (w : Window 3)
    (H : IsJet3AtOrder m z w) :
    w = xiJet3AtOrder m z := by
  -- Unfold `IsJet3AtOrder` to `IsJet3At (cderivIter m Xi) z w`
  have Hcanon : IsJet3AtOrder m z (xiJet3AtOrder m z) :=
    isJet3AtOrder_xiJet3AtOrder (m := m) (z := z)
  -- Reduce to the generic Jet3 uniqueness lemma.
  -- (`IsJet3AtOrder` is definitional `IsJet3At`.)
  exact window_eq_of_isJet3At (F := cderivIter m Xi) (z := z) (w₁ := w) (w₂ := xiJet3AtOrder m z) H Hcanon

/--
Pack the three window equalities from three jet predicates.

This is the recommended analytic interface: prove jet predicates (often via Taylor),
then obtain the window equalities deterministically.
-/
theorem xiJetWindowEqAtOrder_ofJets
    (m : ℕ) (s : OffSeed Xi)
    (Hw0  : IsJet3AtOrder m (z_w0At s)  (w0At  m s))
    (Hwp2 : IsJet3AtOrder m (z_wp2At s) (wp2At m s))
    (Hwp3 : IsJet3AtOrder m (z_wp3At s) (wp3At m s)) :
    XiJetWindowEqAtOrder m s := by
  refine ⟨?_, ?_, ?_⟩
  · -- w0At
    simpa using (window_eq_xiJet3AtOrder_of_isJet3AtOrder (m := m) (z := z_w0At s) (w := w0At m s) Hw0)
  · -- wp2At
    simpa using (window_eq_xiJet3AtOrder_of_isJet3AtOrder (m := m) (z := z_wp2At s) (w := wp2At m s) Hwp2)
  · -- wp3At
    simpa using (window_eq_xiJet3AtOrder_of_isJet3AtOrder (m := m) (z := z_wp3At s) (w := wp3At m s) Hwp3)

/--
Optional convenience: a provider class for the *jet predicates*,
from which we can build the existing window-equality provider.
-/
class XiJetWindowIsJetAtOrderProvider : Type where
  jet_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrder m (z_w0At s)  (w0At  m s)
  jet_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrder m (z_wp2At s) (wp2At m s)
  jet_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrder m (z_wp3At s) (wp3At m s)

/-- If you can provide jets, you automatically get the window-equality provider. -/
instance (P : XiJetWindowIsJetAtOrderProvider) : XiJetWindowEqAtOrderProvider where
  windowEqAtOrder := by
    intro m s
    exact xiJetWindowEqAtOrder_ofJets (m := m) (s := s)
      (Hw0 := P.jet_w0At m s)
      (Hwp2 := P.jet_wp2At m s)
      (Hwp3 := P.jet_wp3At m s)

end TAC

end XiPacket
end Targets
end Hyperlocal
