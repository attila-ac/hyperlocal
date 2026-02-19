/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateFromAnalytic.lean

  FIX (Lean 4.23-rc2):
    `theorem` must have a Prop type. Here the "alias" returns a Type
    (`XiJetQuotRow0ConcreteExtractAtOrder m s`), so it must be a `def`.

  This file stays cycle-safe: it imports only GateDefs + the Route–B endpoint module,
  not the Gate axiom/heart/frontier.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderScalarize
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderFromRecurrenceB

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport
open Hyperlocal.Cancellation  -- brings `convCoeff` into scope

/-- Local alias: the Route–B endpoint feeding the AtOrder Gate glue (Type-valued, so `def`). -/
noncomputable def xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0ConcreteExtractAtOrder m s :=
  xiJetQuotRow0ConcreteExtractAtOrder_fromRecurrenceB (m := m) (s := s)

/-- Build `Row0ConvolutionAtRev` for `w0At m s` from the analytic Toeplitz witness. -/
theorem row0ConvolutionAtRev_w0At_fromAnalytic (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (s.ρ) (w0At m s) := by
  classical
  rcases JetQuotOp.xiRouteA_jetPkg (s := s) (z := s.ρ) (w := w0At m s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have E : XiJetQuotRow0ConcreteExtractAtOrder m s :=
    xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)
  have GS : XiJetQuotRow0ScalarGoalsAtOrder m s :=
    scalarGoalsAtOrder_of_extract (m := m) (s := s) E

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
    have := GS.hw0At
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using this

  exact ⟨G, hfac, hjet, h3⟩

/-- Build `Row0ConvolutionAtRev` for `wp2At m s` from the analytic Toeplitz witness. -/
theorem row0ConvolutionAtRev_wp2At_fromAnalytic (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  rcases JetQuotOp.xiRouteA_jetPkg
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have E : XiJetQuotRow0ConcreteExtractAtOrder m s :=
    xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)
  have GS : XiJetQuotRow0ScalarGoalsAtOrder m s :=
    scalarGoalsAtOrder_of_extract (m := m) (s := s) E

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
    have := GS.hwp2At
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using this

  exact ⟨G, hfac, hjet, h3⟩

/-- Build `Row0ConvolutionAtRev` for `wp3At m s` from the analytic Toeplitz witness. -/
theorem row0ConvolutionAtRev_wp3At_fromAnalytic (m : ℕ) (s : OffSeed Xi) :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  rcases JetQuotOp.xiRouteA_jetPkg
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have E : XiJetQuotRow0ConcreteExtractAtOrder m s :=
    xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)
  have GS : XiJetQuotRow0ScalarGoalsAtOrder m s :=
    scalarGoalsAtOrder_of_extract (m := m) (s := s) E

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
    have := GS.hwp3At
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using this

  exact ⟨G, hfac, hjet, h3⟩

/-- Package the three AtOrder Row--0 convolution facts (discharged from analytic Toeplitz witness). -/
theorem xiJetQuotRow0AtOrderConvolutionOut_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0AtOrderConvolutionOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row0ConvolutionAtRev_w0At_fromAnalytic (m := m) (s := s)
  · exact row0ConvolutionAtRev_wp2At_fromAnalytic (m := m) (s := s)
  · exact row0ConvolutionAtRev_wp3At_fromAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
