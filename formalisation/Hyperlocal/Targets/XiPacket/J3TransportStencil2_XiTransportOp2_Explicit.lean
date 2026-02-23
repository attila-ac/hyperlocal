/-
  Hyperlocal/Targets/XiPacket/J3TransportStencil2_XiTransportOp2_Explicit.lean

  Step 1 (cycle-safe): combine
    - TAC.transportLower3_eq_stencil
    - TAC.XiTransportOp₂_eq_transportLower
  to get an explicit δ-stencil formula for XiTransportOp 2.
-/

import Hyperlocal.Targets.XiPacket.J3TransportStencil2_CoeffMatch
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_XiTransportCompat

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

/-- Explicit stencil formula for `XiTransportOp 2` (the one you want for J3 matching). -/
theorem XiTransportOp₂_eq_explicit_stencil
    (s : Hyperlocal.OffSeed Xi) (w : Window 3) :
    (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w
      =
    ![
      w 0,
      (w 1) + ((delta s : ℝ) : ℂ) * (w 0),
      (w 2) + ((delta s : ℝ) : ℂ) * (w 1)
        + ((((delta s : ℝ) : ℂ) ^ 2) / (2 : ℂ)) * (w 0)
    ] := by
  classical
  -- use compat: XiTransportOp 2 s = transportLower 3 (delta s)
  have hcompat :=
    (TAC.XiTransportOp₂_eq_transportLower (s := s) (w := w))
  -- rewrite RHS via your explicit transportLower(3) stencil lemma
  -- `hcompat` is an equality of functions, so apply `congrArg` at each coordinate by ext/fin_cases
  funext i
  -- evaluate the function equality at i
  have hi :
      (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) w i
        =
      TAC.transportLower 3 (((delta s : ℝ) : ℂ)) w i := by
    simpa using congrArg (fun f => f i) hcompat
  -- now use your explicit transportLower3 lemma
  -- (transportLower3_eq_stencil is an equality of functions too)
  have hst :
      TAC.transportLower 3 (((delta s : ℝ) : ℂ)) w
        =
      ![
        w 0,
        (w 1) + (((delta s : ℝ) : ℂ)) * (w 0),
        (w 2) + (((delta s : ℝ) : ℂ)) * (w 1)
          + ((((delta s : ℝ) : ℂ) ^ 2) / (2 : ℂ)) * (w 0)
      ] := by
    simpa using (transportLower3_eq_stencil (δ := ((delta s : ℝ) : ℂ)) (w := w))
  -- finish coordinatewise
  -- `hst` is equality of functions, so again evaluate at i
  have hi2 :
      TAC.transportLower 3 (((delta s : ℝ) : ℂ)) w i
        =
      (![
        w 0,
        (w 1) + (((delta s : ℝ) : ℂ)) * (w 0),
        (w 2) + (((delta s : ℝ) : ℂ)) * (w 1)
          + ((((delta s : ℝ) : ℂ) ^ 2) / (2 : ℂ)) * (w 0)
      ] : Window 3) i := by
    simpa using congrArg (fun f => f i) hst
  exact hi.trans hi2

end TAC

end XiPacket
end Targets
end Hyperlocal
