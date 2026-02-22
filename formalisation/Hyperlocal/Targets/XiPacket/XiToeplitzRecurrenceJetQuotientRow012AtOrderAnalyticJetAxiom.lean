/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom.lean

  Non-cycle-safe analytic axiom layer (draft):

  Extends the existing row012 scalar payload by adding the *jet interpretation*:
  each of the three windows is a genuine 3-jet of `Xi` at its intended anchor.

  This is the minimal statement needed to discharge Step B sorries
  WITHOUT pretending any false Taylor identity in ℂ.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target
import Hyperlocal.Targets.XiPacket.XiJet3Defs
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

/-- Same anchors as in your Step-B instances file. -/
abbrev z_w0At (s : OffSeed Xi) : ℂ := sc s + ((delta s : ℝ) : ℂ)
abbrev z_wp2At (s : OffSeed Xi) : ℂ := (starRingEnd ℂ) s.ρ
abbrev z_wp3At (s : OffSeed Xi) : ℂ := 1 - (starRingEnd ℂ) s.ρ

/--
Analytic row012 package with jet interpretation.

This is the *exact* additional semantic content Step B needs.
-/
structure XiJetQuotRow012AtOrder_AnalyticJet (m : ℕ) (s : OffSeed Xi) : Type where
  base : XiJetQuotRow012AtOrder m s
  jet_w0At  : IsJet3At Xi (z_w0At s) (w0At m s)
  jet_wp2At : IsJet3At Xi (z_wp2At s) (wp2At m s)
  jet_wp3At : IsJet3At Xi (z_wp3At s) (wp3At m s)

/--
Primitive endpoint (axiom for now): analytic extractor produces the analytic-jet package.
Later you *prove* this from your jet/quotient model semantics (mod w^3).
-/
axiom xiJetQuotRow012AtOrder_analyticJet
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012AtOrder_AnalyticJet m s

end TAC

end XiPacket
end Targets
end Hyperlocal
