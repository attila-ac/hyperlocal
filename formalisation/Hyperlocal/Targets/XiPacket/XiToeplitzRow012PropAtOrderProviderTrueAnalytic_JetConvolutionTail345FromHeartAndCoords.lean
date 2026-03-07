/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345FromHeartAndCoords.lean

  Push C (finite algebra): discharge the 9 tail convolution equalities (n=3,4,5)
  for the three canonical AtOrder windows (w0At/wp2At/wp3At).

  Strategy (cycle-safe):
    * obtain the Row0 heart equalities (row0Sigma = 0) from the sigma provider,
    * obtain coords(0,1) for the three windows,
    * use the purely algebraic builder
        xiRow012ConvolutionAtRevAtOrderOut_of_heart_and_coords
      to manufacture Row012ConvolutionAtRev for each window,
    * project the 9 convCoeff equalities.

  IMPORTANT:
    `XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromHeartAndCoords.lean`
    is now theorem-side and explicitly requires

        [TAC.XiJetWindowEqAtOrderQuotProvider]

    Therefore this consumer must thread that gate honestly as well.

  Output:
    An instance of the manuscript tail class
      XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript
    which is immediately upgraded to the real tail class
      XiJetConvolutionTail345AtOrderTrueAnalytic
    by the adapter instance already present in
      `XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromHeartAndCoords

-- Tail345 manuscript interface + adapter to the real Tail345 class.
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Helper: extract the three tail equalities from a `Row012ConvolutionAtRev` witness. -/
private theorem tail345_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 := by
  classical
  rcases H with ⟨G, hfac, hjet, h3, h4, h5⟩
  exact ⟨h3, h4, h5⟩

/-- Push C: tail(3/4/5) for `w0At` from heart+coords. -/
theorem tail345_w0At_from_heart_and_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0 := by
  classical
  have Hheart : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)
  have Hcoords : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  have Hrow012 : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_of_heart_and_coords
      (m := m) (s := s) Hheart Hcoords
  exact tail345_of_row012ConvolutionAtRev
    (s := s) (z := s.ρ) (w := w0At m s) Hrow012.hw0At

/-- Push C: tail(3/4/5) for `wp2At` from heart+coords. -/
theorem tail345_wp2At_from_heart_and_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0 := by
  classical
  have Hheart : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)
  have Hcoords : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  have Hrow012 : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_of_heart_and_coords
      (m := m) (s := s) Hheart Hcoords
  exact tail345_of_row012ConvolutionAtRev
    (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) Hrow012.hwp2At

/-- Push C: tail(3/4/5) for `wp3At` from heart+coords. -/
theorem tail345_wp3At_from_heart_and_coords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0 := by
  classical
  have Hheart : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)
  have Hcoords : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  have Hrow012 : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_of_heart_and_coords
      (m := m) (s := s) Hheart Hcoords
  exact tail345_of_row012ConvolutionAtRev
    (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) Hrow012.hwp3At

/--
Install the Tail345 manuscript payload.

Downstream, the adapter instance in
`XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Manuscript.lean`
upgrades this to `XiJetConvolutionTail345AtOrderTrueAnalytic`.
-/
instance (priority := 1000)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetConvolutionTail345AtOrderTrueAnalytic_Manuscript where
  tail3_w0At := by
    intro m s
    exact (tail345_w0At_from_heart_and_coords (m := m) (s := s)).1
  tail4_w0At := by
    intro m s
    exact (tail345_w0At_from_heart_and_coords (m := m) (s := s)).2.1
  tail5_w0At := by
    intro m s
    exact (tail345_w0At_from_heart_and_coords (m := m) (s := s)).2.2
  tail3_wp2At := by
    intro m s
    exact (tail345_wp2At_from_heart_and_coords (m := m) (s := s)).1
  tail4_wp2At := by
    intro m s
    exact (tail345_wp2At_from_heart_and_coords (m := m) (s := s)).2.1
  tail5_wp2At := by
    intro m s
    exact (tail345_wp2At_from_heart_and_coords (m := m) (s := s)).2.2
  tail3_wp3At := by
    intro m s
    exact (tail345_wp3At_from_heart_and_coords (m := m) (s := s)).1
  tail4_wp3At := by
    intro m s
    exact (tail345_wp3At_from_heart_and_coords (m := m) (s := s)).2.1
  tail5_wp3At := by
    intro m s
    exact (tail345_wp3At_from_heart_and_coords (m := m) (s := s)).2.2

end XiPacket
end Targets
end Hyperlocal
