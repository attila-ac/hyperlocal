/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProvider.lean

  Step 4 refactor target:
  Replace the hidden global axiom `xiJetWindowEqAtOrder` by an explicit typeclass provider.

  This file contains NO axioms.

  Downstream code should import this file (provider surface) rather than the axiom installer.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Analysis.Calculus.Deriv.Basic

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

abbrev z_w0At (s : OffSeed Xi) : ℂ := sc s + ((delta s : ℝ) : ℂ)
abbrev z_wp2At (s : OffSeed Xi) : ℂ := (starRingEnd ℂ) s.ρ
abbrev z_wp3At (s : OffSeed Xi) : ℂ := 1 - (starRingEnd ℂ) s.ρ

/--
Minimal remaining semantic cliff: the three window=canonical-jet equalities.
-/
structure XiJetWindowEqAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  w0At_eq_xiJet3AtOrder  : w0At m s  = xiJet3AtOrder m (z_w0At s)
  wp2At_eq_xiJet3AtOrder : wp2At m s = xiJet3AtOrder m (z_wp2At s)
  wp3At_eq_xiJet3AtOrder : wp3At m s = xiJet3AtOrder m (z_wp3At s)

/--
Step 4: explicit provider surface (typeclass).

This replaces the old global axiom `xiJetWindowEqAtOrder`.
-/
class XiJetWindowEqAtOrderProvider : Type where
  windowEqAtOrder : ∀ (m : ℕ) (s : OffSeed Xi), XiJetWindowEqAtOrder m s

/-- The canonical accessor (now explicit in the typeclass). -/
noncomputable def xiJetWindowEqAtOrder
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    XiJetWindowEqAtOrder m s :=
  XiJetWindowEqAtOrderProvider.windowEqAtOrder m s

/--
The combined package used downstream:

* `base` is theorem-level from the analytic-upstream pipeline.
* window equalities come from `[XiJetWindowEqAtOrderProvider]`.
-/
structure XiJetQuotRow012AtOrder_AnalyticJet (m : ℕ) (s : OffSeed Xi) : Type where
  base : XiJetQuotRow012AtOrder m s
  w0At_eq_xiJet3AtOrder  : w0At m s  = xiJet3AtOrder m (z_w0At s)
  wp2At_eq_xiJet3AtOrder : wp2At m s = xiJet3AtOrder m (z_wp2At s)
  wp3At_eq_xiJet3AtOrder : wp3At m s = xiJet3AtOrder m (z_wp3At s)

namespace XiJetQuotRow012AtOrder_AnalyticJet

variable {m : ℕ} {s : OffSeed Xi}

theorem jet_w0At (P : XiJetQuotRow012AtOrder_AnalyticJet m s) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) := by
  simpa [IsJet3AtOrder, P.w0At_eq_xiJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_w0At s))

theorem jet_wp2At (P : XiJetQuotRow012AtOrder_AnalyticJet m s) :
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) := by
  simpa [IsJet3AtOrder, P.wp2At_eq_xiJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp2At s))

theorem jet_wp3At (P : XiJetQuotRow012AtOrder_AnalyticJet m s) :
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  simpa [IsJet3AtOrder, P.wp3At_eq_xiJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp3At s))

end XiJetQuotRow012AtOrder_AnalyticJet

/--
Exported endpoint (same name intent as before):

Now definitionally uses the theorem-level upstream base payload,
and depends on `[XiJetWindowEqAtOrderProvider]` for the window equalities.
-/
noncomputable def xiJetQuotRow012AtOrder_analyticJet
    (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    XiJetQuotRow012AtOrder_AnalyticJet m s :=
  { base := Hyperlocal.Targets.XiPacket.xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s)
    w0At_eq_xiJet3AtOrder  := (xiJetWindowEqAtOrder (m := m) (s := s)).w0At_eq_xiJet3AtOrder
    wp2At_eq_xiJet3AtOrder := (xiJetWindowEqAtOrder (m := m) (s := s)).wp2At_eq_xiJet3AtOrder
    wp3At_eq_xiJet3AtOrder := (xiJetWindowEqAtOrder (m := m) (s := s)).wp3At_eq_xiJet3AtOrder }

end TAC

end XiPacket
end Targets
end Hyperlocal
