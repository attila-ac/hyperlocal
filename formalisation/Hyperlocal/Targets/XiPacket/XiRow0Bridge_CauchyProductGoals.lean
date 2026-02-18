/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyProductGoals.lean

  Route--C Row--0 scalar goals, sourced from the Cauchy/convolution bridge.

  IMPORTANT:
  Root-level names `Hyperlocal.Targets.XiPacket.row0Sigma_*_eq_zero` and `..._eq_eval`
  are already declared elsewhere in the repository state (per Lean error).
  Therefore this file must NOT redeclare them.

  This file provides namespaced aliases (non-clashing) under `RouteCRow0Goals`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace RouteCRow0Goals

/-- Alias of the already-declared root theorem. -/
abbrev row0Sigma_w0_eq_zero (s : OffSeed Xi) : row0Sigma s (w0 s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_w0_eq_zero s

abbrev row0Sigma_wc_eq_zero (s : OffSeed Xi) : row0Sigma s (wc s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_zero s

abbrev row0Sigma_wp2_eq_zero (s : OffSeed Xi) : row0Sigma s (wp2 s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wp2_eq_zero s

abbrev row0Sigma_wp3_eq_zero (s : OffSeed Xi) : row0Sigma s (wp3 s) = 0 :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wp3_eq_zero s

abbrev row0Sigma_w0_eq_eval (s : OffSeed Xi) :
    row0Sigma s (w0 s) = (Rquartet s.ρ).eval (s.ρ) :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_w0_eq_eval s

abbrev row0Sigma_wc_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wc s) = (Rquartet s.ρ).eval (1 - s.ρ) :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wc_eq_eval s

abbrev row0Sigma_wp2_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wp2 s) = (Rquartet s.ρ).eval ((starRingEnd ℂ) s.ρ) :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wp2_eq_eval s

abbrev row0Sigma_wp3_eq_eval (s : OffSeed Xi) :
    row0Sigma s (wp3 s) = (Rquartet s.ρ).eval (1 - (starRingEnd ℂ) s.ρ) :=
  _root_.Hyperlocal.Targets.XiPacket.row0Sigma_wp3_eq_eval s

end RouteCRow0Goals

end XiPacket
end Targets
end Hyperlocal
