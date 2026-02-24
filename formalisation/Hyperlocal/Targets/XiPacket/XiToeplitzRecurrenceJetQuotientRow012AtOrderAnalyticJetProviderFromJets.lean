/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets.lean

  Step 4.5 (bridge): derive window=canonical-jet equalities from *jet facts*.

  Motivation:
    The remaining analytic cliff was refactored into explicit provider classes.

    In practice, it is often easier to prove jet predicates
      IsJet3AtOrder m z (w?At m s)
    than to prove raw window equalities. This file provides the deterministic
    conversion:

      IsJet3AtOrder m z w  ⇒  w = xiJet3AtOrder m z

    and then packages the three equalities into `XiJetWindowEqAtOrder m s`.

  This file contains NO axioms.

  ---
  Option B / quotient jets:
    We also provide the parallel deterministic conversion for

      IsJet3AtOrderQuot m s z w

    whose canonical window is `jet3 (routeA_G s) z`.

  NOTE (Lean 4.23 rc2 snapshot quirk):
    In this repo, `jet3` / `isJet3At_jet3` live in
    `XiRow0Bridge_JetLeibnizAt_Discharge.lean`, but importing that is too heavy here.
    So we re-declare the tiny definitional `jet3` *locally*, with the simp lemmas
    needed for numeral indices `(0 : Fin 3)` etc.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProvider
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs

import Mathlib.Analysis.Calculus.Deriv.Basic
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

/-
  Local copy of the repo’s “raw derivative jet window” (length 3).

  We keep this local so this bridge file does NOT need to import the
  Route-L discharge module just to access `jet3` and `isJet3At_jet3`.
-/

/-- Canonical raw-derivative jet window of length 3 for `G` at `z`. -/
def jet3 (G : ℂ → ℂ) (z : ℂ) : Transport.Window 3 :=
  fun i =>
    match i.1 with
    | 0 => G z
    | 1 => deriv G z
    | _ => deriv (deriv G) z

-- simp lemmas for subtype-style indices
@[simp] lemma jet3_coord0 (G : ℂ → ℂ) (z : ℂ) :
    jet3 G z ⟨0, by decide⟩ = G z := by
  simp [jet3]

@[simp] lemma jet3_coord1 (G : ℂ → ℂ) (z : ℂ) :
    jet3 G z ⟨1, by decide⟩ = deriv G z := by
  simp [jet3]

@[simp] lemma jet3_coord2 (G : ℂ → ℂ) (z : ℂ) :
    jet3 G z ⟨2, by decide⟩ = deriv (deriv G) z := by
  simp [jet3]

-- simp lemmas for numeral `Fin` indices (this is the missing piece in your attempt)
@[simp] lemma jet3_coord0' (G : ℂ → ℂ) (z : ℂ) :
    jet3 G z (0 : Fin 3) = G z := by
  -- `0 : Fin 3` is definitional equal to `⟨0, _⟩`
  simpa using (jet3_coord0 (G := G) (z := z))

@[simp] lemma jet3_coord1' (G : ℂ → ℂ) (z : ℂ) :
    jet3 G z (1 : Fin 3) = deriv G z := by
  simpa using (jet3_coord1 (G := G) (z := z))

@[simp] lemma jet3_coord2' (G : ℂ → ℂ) (z : ℂ) :
    jet3 G z (2 : Fin 3) = deriv (deriv G) z := by
  simpa using (jet3_coord2 (G := G) (z := z))

/-- Jet tautology: `jet3 G z` is a Jet3 window for `G` at `z`. -/
lemma isJet3At_jet3 (G : ℂ → ℂ) (z : ℂ) :
    IsJet3At G z (jet3 G z) := by
  constructor
  · -- coordinate 0 (the goal is stated at `0 : Fin 3` in this repo)
    simpa using (jet3_coord0' (G := G) (z := z))
  constructor
  · -- coordinate 1
    simpa using (jet3_coord1' (G := G) (z := z))
  · -- coordinate 2
    simpa using (jet3_coord2' (G := G) (z := z))

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

/-- Pack the three window equalities from three jet predicates (original provider). -/
theorem mk_XiJetWindowEqAtOrder
    (m : ℕ) (s : OffSeed Xi)
    (H0 : IsJet3AtOrder m (z_w0At s) (w0At m s))
    (H2 : IsJet3AtOrder m (z_wp2At s) (wp2At m s))
    (H3 : IsJet3AtOrder m (z_wp3At s) (wp3At m s)) :
    XiJetWindowEqAtOrder m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact window_eq_xiJet3AtOrder_of_isJet3AtOrder (m := m) (z := z_w0At s) (w := w0At m s) H0
  · exact window_eq_xiJet3AtOrder_of_isJet3AtOrder (m := m) (z := z_wp2At s) (w := wp2At m s) H2
  · exact window_eq_xiJet3AtOrder_of_isJet3AtOrder (m := m) (z := z_wp3At s) (w := wp3At m s) H3

/-- Optional: a provider class for jet predicates (original, non-quotient). -/
class XiJetWindowIsJetAtOrderProvider : Type where
  jet_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrder m (z_w0At s)  (w0At  m s)
  jet_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrder m (z_wp2At s) (wp2At m s)
  jet_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrder m (z_wp3At s) (wp3At m s)

/-- If you can provide jets, you automatically get the window-equality provider. -/
instance (P : XiJetWindowIsJetAtOrderProvider) : XiJetWindowEqAtOrderProvider where
  windowEqAtOrder := by
    intro m s
    exact mk_XiJetWindowEqAtOrder (m := m) (s := s)
      (H0 := P.jet_w0At m s)
      (H2 := P.jet_wp2At m s)
      (H3 := P.jet_wp3At m s)

--------------------------------------------------------------------------------
-- Option B / quotient jets: deterministic conversion + packaging (axiom-free)
--------------------------------------------------------------------------------

/-- Quotient window-equality bundle: concrete windows equal the canonical `jet3 (routeA_G s) z_*`. -/
structure XiJetWindowEqAtOrderQuot (m : ℕ) (s : OffSeed Xi) : Prop where
  w0At_eq  : w0At  m s = jet3 (routeA_G s) (z_w0At s)
  wp2At_eq : wp2At m s = jet3 (routeA_G s) (z_wp2At s)
  wp3At_eq : wp3At m s = jet3 (routeA_G s) (z_wp3At s)

/-- Provider of quotient window equalities (the “eq” surface). -/
class XiJetWindowEqAtOrderQuotProvider : Prop where
  windowEqAtOrderQuot : ∀ (m : ℕ) (s : OffSeed Xi), XiJetWindowEqAtOrderQuot m s

/-- Provider of quotient jet facts (the “isJet” surface). -/
class XiJetWindowIsJetAtOrderQuotProvider : Prop where
  jet_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (z_w0At s) (w0At m s)
  jet_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (z_wp2At s) (wp2At m s)
  jet_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), IsJet3AtOrderQuot m s (z_wp3At s) (wp3At m s)

/-- Canonicalization lemma for quotient jets: `IsJet3AtOrderQuot` ⇒ equality with `jet3 (routeA_G s) z`. -/
theorem window_eq_jet3_routeA_of_isJet3AtOrderQuot
    (m : ℕ) (s : OffSeed Xi) (z : ℂ) (w : Window 3)
    (H : IsJet3AtOrderQuot m s z w) :
    w = jet3 (routeA_G s) z := by
  have Hcanon : IsJet3At (routeA_G s) z (jet3 (routeA_G s) z) :=
    isJet3At_jet3 (routeA_G s) z
  have H' : IsJet3At (routeA_G s) z w := by
    simpa [IsJet3AtOrderQuot] using H
  exact window_eq_of_isJet3At (F := routeA_G s) (z := z) (w₁ := w) (w₂ := jet3 (routeA_G s) z) H' Hcanon

/-- Package three quotient-window equalities from three quotient jet predicates. -/
theorem mk_XiJetWindowEqAtOrderQuot
    (m : ℕ) (s : OffSeed Xi)
    (H0 : IsJet3AtOrderQuot m s (z_w0At s) (w0At m s))
    (H2 : IsJet3AtOrderQuot m s (z_wp2At s) (wp2At m s))
    (H3 : IsJet3AtOrderQuot m s (z_wp3At s) (wp3At m s)) :
    XiJetWindowEqAtOrderQuot m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact window_eq_jet3_routeA_of_isJet3AtOrderQuot (m := m) (s := s) (z := z_w0At s) (w := w0At m s) H0
  · exact window_eq_jet3_routeA_of_isJet3AtOrderQuot (m := m) (s := s) (z := z_wp2At s) (w := wp2At m s) H2
  · exact window_eq_jet3_routeA_of_isJet3AtOrderQuot (m := m) (s := s) (z := z_wp3At s) (w := wp3At m s) H3

/-- Install the quotient eq-provider from the quotient isJet-provider. -/
instance (P : XiJetWindowIsJetAtOrderQuotProvider) : XiJetWindowEqAtOrderQuotProvider where
  windowEqAtOrderQuot := by
    intro m s
    exact mk_XiJetWindowEqAtOrderQuot (m := m) (s := s)
      (H0 := P.jet_w0At m s)
      (H2 := P.jet_wp2At m s)
      (H3 := P.jet_wp3At m s)

end TAC

end XiPacket
end Targets
end Hyperlocal
