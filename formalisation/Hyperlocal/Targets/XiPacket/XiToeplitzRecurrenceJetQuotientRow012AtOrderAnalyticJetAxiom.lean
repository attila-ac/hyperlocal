/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom.lean

  Non-cycle-safe analytic axiom layer (draft):

  Adds the *jet interpretation* in the correct order-`m` sense:

    w0At m s  = xiJet3AtOrder m (z_w0At s)
    wp2At m s = xiJet3AtOrder m (z_wp2At s)
    wp3At m s = xiJet3AtOrder m (z_wp3At s)

  This is the minimal “semantic cliff” that can later be proved from the
  truncated-jet/quotient semantics (where the transport truncation becomes exact).
-/

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

structure XiJetQuotRow012AtOrder_AnalyticJet (m : ℕ) (s : OffSeed Xi) : Type where
  base : XiJetQuotRow012AtOrder m s
  w0At_eq_xiJet3AtOrder  : w0At m s  = xiJet3AtOrder m (z_w0At s)
  wp2At_eq_xiJet3AtOrder : wp2At m s = xiJet3AtOrder m (z_wp2At s)
  wp3At_eq_xiJet3AtOrder : wp3At m s = xiJet3AtOrder m (z_wp3At s)

namespace XiJetQuotRow012AtOrder_AnalyticJet

variable {m : ℕ} {s : OffSeed Xi}

theorem jet_w0At (P : XiJetQuotRow012AtOrder_AnalyticJet m s) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) := by
  -- rewrite to canonical order-m jet window
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

axiom xiJetQuotRow012AtOrder_analyticJet
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012AtOrder_AnalyticJet m s

end TAC

end XiPacket
end Targets
end Hyperlocal
