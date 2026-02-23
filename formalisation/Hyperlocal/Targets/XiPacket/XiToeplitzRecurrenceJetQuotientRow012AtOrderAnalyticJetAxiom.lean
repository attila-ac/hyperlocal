/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom.lean

  Non-cycle-safe analytic axiom layer (refined):

  OLD: axiomatized a whole structure containing both:
    * the Row012 target bundle `XiJetQuotRow012AtOrder m s`
    * plus the three window=jet equalities.

  NEW: the Row012 target bundle is already theorem-level from the upstream analytic proof
  stack (`...AnalyticProofUpstream.lean`).  So we *define* `base` from that theorem-level
  provider, and axiomatize only the minimal remaining semantic cliff:

    w0At m s  = xiJet3AtOrder m (z_w0At s)
    wp2At m s = xiJet3AtOrder m (z_wp2At s)
    wp3At m s = xiJet3AtOrder m (z_wp3At s)

  This matches the recommended “shrink the cliff to window equality” playbook.
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

We keep this as a dedicated *axiom surface* so the rest of the file can be theorem-level.
-/
structure XiJetWindowEqAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  w0At_eq_xiJet3AtOrder  : w0At m s  = xiJet3AtOrder m (z_w0At s)
  wp2At_eq_xiJet3AtOrder : wp2At m s = xiJet3AtOrder m (z_wp2At s)
  wp3At_eq_xiJet3AtOrder : wp3At m s = xiJet3AtOrder m (z_wp3At s)

/--
The combined package used downstream:

* `base` is now theorem-level from the analytic-upstream pipeline.
* The only remaining axioms are the three window equalities.
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
Primitive axiom: only the window=jet equalities remain axiomatic.
-/
axiom xiJetWindowEqAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetWindowEqAtOrder m s

/--
Exported endpoint (same name as before; downstream unchanged):

Now **definitionally** uses the theorem-level upstream base payload, and
the only remaining axiom use is `xiJetWindowEqAtOrder`.
-/
noncomputable def xiJetQuotRow012AtOrder_analyticJet
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder_AnalyticJet m s :=
  { base := Hyperlocal.Targets.XiPacket.xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s)
    w0At_eq_xiJet3AtOrder  := (xiJetWindowEqAtOrder (m := m) (s := s)).w0At_eq_xiJet3AtOrder
    wp2At_eq_xiJet3AtOrder := (xiJetWindowEqAtOrder (m := m) (s := s)).wp2At_eq_xiJet3AtOrder
    wp3At_eq_xiJet3AtOrder := (xiJetWindowEqAtOrder (m := m) (s := s)).wp3At_eq_xiJet3AtOrder }

end TAC

end XiPacket
end Targets
end Hyperlocal
