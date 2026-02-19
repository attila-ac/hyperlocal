/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischargeAtOrder.lean

  Discharge `Row0ConvolutionAtRev` for AtOrder windows.

  CHANGE (2026-02-19): this file is now a compatibility export layer.
  The AtOrder Gate is the single semantic insertion point, so we simply
  project the three convolution facts from:

    `xiJetQuotRow0AtOrderConvolutionOut m s`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGate

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Build `Row0ConvolutionAtRev` for `w0At`. -/
theorem row0ConvolutionAtRev_w0At (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (s.ρ) (w0At m s) := by
  exact (xiJetQuotRow0AtOrderConvolutionOut (m := m) (s := s)).hw0At

/-- Build `Row0ConvolutionAtRev` for `wp2At`. -/
theorem row0ConvolutionAtRev_wp2At (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  exact (xiJetQuotRow0AtOrderConvolutionOut (m := m) (s := s)).hwp2At

/-- Build `Row0ConvolutionAtRev` for `wp3At`. -/
theorem row0ConvolutionAtRev_wp3At (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  exact (xiJetQuotRow0AtOrderConvolutionOut (m := m) (s := s)).hwp3At

end XiPacket
end Targets
end Hyperlocal
