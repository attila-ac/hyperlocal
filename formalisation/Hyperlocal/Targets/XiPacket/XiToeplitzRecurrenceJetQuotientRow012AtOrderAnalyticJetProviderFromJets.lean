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

  ---
  ADDITION (Option B / quotient jets):
    We also provide the parallel deterministic conversion for

      IsJet3AtOrderQuot m s z w

    whose canonical window is `jet3 (routeA_G s) z`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProvider
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA

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
  fin_cases i <;>
    rcases H₁ with ⟨h10, h11, h12⟩ <;>
    rcases H₂ with ⟨h20, h21, h22⟩ <;>
    simp_all

/--
Canonicalization lemma (order-m):

If `w` is an order-m jet of `Xi` at `z`, then it equals the canonical jet window
`xiJet3AtOrder m z`.
-/
theorem window_eq_xiJet3AtOrder_of_isJet3AtOrder
    (m : ℕ) (z : ℂ) (w : Window 3)
    (H : IsJet3AtOrder m z w) :
    w = xiJet3AtOrder m z := by
  have Hcanon : IsJet3AtOrder m z (xiJet3AtOrder m z) :=
    isJet3AtOrder_xiJet3AtOrder (m := m) (z := z)
  exact window_eq_of_isJet3At
    (F := cderivIter m Xi) (z := z) (w₁ := w) (w₂ := xiJet3AtOrder m z) H Hcanon

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
  · simpa using (window_eq_xiJet3AtOrder_of_isJet3AtOrder
      (m := m) (z := z_w0At s) (w := w0At m s) Hw0)
  · simpa using (window_eq_xiJet3AtOrder_of_isJet3AtOrder
      (m := m) (z := z_wp2At s) (w := wp2At m s) Hwp2)
  · simpa using (window_eq_xiJet3AtOrder_of_isJet3AtOrder
      (m := m) (z := z_wp3At s) (w := wp3At m s) Hwp3)

/-- Optional convenience: a provider class for the *jet predicates*,
from which we can build the existing window-equality provider. -/
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

--------------------------------------------------------------------------------
-- Option B / quotient jets: parallel deterministic conversion + packaging
--------------------------------------------------------------------------------

/--
Quotient-window equality package:

These are the three concrete equalities your Route-A bridge axioms already target.
We keep the `m` parameter for API alignment with the rest of the pipeline.
-/
structure XiJetWindowEqAtOrderQuot (m : ℕ) (s : OffSeed Xi) : Prop where
  w0At_eq  : w0At  m s = jet3 (routeA_G s) (s.ρ)
  wp2At_eq : wp2At m s = jet3 (routeA_G s) ((starRingEnd ℂ) s.ρ)
  wp3At_eq : wp3At m s = jet3 (routeA_G s) (1 - (starRingEnd ℂ) s.ρ)

/--
Canonicalization lemma (quotient jet):

If `w` is a quotient-jet of `routeA_G s` at `z`, then it equals `jet3 (routeA_G s) z`.
-/
theorem window_eq_jet3_routeA_of_isJet3AtOrderQuot
    (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H : IsJet3AtOrderQuot m s z w) :
    w = jet3 (routeA_G s) z := by
  have Hcanon : IsJet3At (routeA_G s) z (jet3 (routeA_G s) z) := by
    simpa using (isJet3At_jet3 (G := routeA_G s) (z := z))
  -- unfold the quotient-jet predicate and use Jet3 uniqueness
  have H' : IsJet3At (routeA_G s) z w := by
    simpa [IsJet3AtOrderQuot] using H
  exact window_eq_of_isJet3At (F := routeA_G s) (z := z) (w₁ := w) (w₂ := jet3 (routeA_G s) z) H' Hcanon

/--
Pack the three quotient-window equalities from three quotient-jet predicates.
-/
theorem xiJetWindowEqAtOrderQuot_ofJets
    (m : ℕ) (s : OffSeed Xi)
    (Hw0  : IsJet3AtOrderQuot m s (s.ρ) (w0At  m s))
    (Hwp2 : IsJet3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s))
    (Hwp3 : IsJet3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)) :
    XiJetWindowEqAtOrderQuot m s := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := s.ρ) (w := w0At m s) Hw0)
  · simpa using (window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) Hwp2)
  · simpa using (window_eq_jet3_routeA_of_isJet3AtOrderQuot
      (m := m) (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) Hwp3)

/-- Provider class (quotient jets) → provider class (quotient window equalities). -/
class XiJetWindowIsJetAtOrderQuotProvider : Prop where
  jet_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (s.ρ) (w0At  m s)
  jet_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  jet_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/-- Window-equality provider (quotient arm). -/
class XiJetWindowEqAtOrderQuotProvider : Prop where
  windowEqAtOrderQuot : ∀ (m : ℕ) (s : OffSeed Xi), XiJetWindowEqAtOrderQuot m s

/-- If you can provide quotient jets, you automatically get quotient window equalities. -/
instance (P : XiJetWindowIsJetAtOrderQuotProvider) : XiJetWindowEqAtOrderQuotProvider where
  windowEqAtOrderQuot := by
    intro m s
    exact xiJetWindowEqAtOrderQuot_ofJets (m := m) (s := s)
      (Hw0 := P.jet_w0At m s)
      (Hwp2 := P.jet_wp2At m s)
      (Hwp3 := P.jet_wp3At m s)

end TAC

end XiPacket
end Targets
end Hyperlocal
