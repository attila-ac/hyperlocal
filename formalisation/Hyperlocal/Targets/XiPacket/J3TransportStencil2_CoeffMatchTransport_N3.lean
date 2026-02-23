/-
  Hyperlocal/Targets/XiPacket/J3TransportStencil2_CoeffMatchTransport_N3.lean

  Step 1 (cycle-safe): match J3 coefficient extraction (N=3) to the explicit
  length-3 transportLower stencil, up to a fixed coordinate convention map.
-/

import Hyperlocal.Transport.ToeplitzInterface
import Hyperlocal.Targets.XiPacket.J3TransportStencil2_CoeffMatch
import Hyperlocal.Targets.XiPacket.J3TransportStencil2_CoeffMatchFull
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC
namespace J3

open Complex
open Hyperlocal.Transport

/-- Base window for transportLower: chosen so transportLower produces coeff1/coeff0 in slots 1/2. -/
def baseWinN3 (a : ℕ → ℂ) : Window 3 :=
  ![ (2 : ℂ) * a 2, a 1, a 0 ]

/-- Post-map from transportLower output to the coeffWin convention:
    take slot 2, then slot 1, then slot 0 divided by 2. -/
def postWinN3 (v : Window 3) : Window 3 :=
  ![ v 2, v 1, v 0 / (2 : ℂ) ]

/--
**Step-1 completion (N=3):** coefficient extraction equals transportLower(3) stencil,
after applying the fixed convention map `postWinN3` and using `baseWinN3`.
-/
theorem coeffWin_eq_post_transportLower_N3 (a : ℕ → ℂ) (δ : ℂ) :
    coeffWin a δ 3
      =
    postWinN3 (TAC.transportLower 3 δ (baseWinN3 a)) := by
  classical

  -- 1️⃣ Expand coeff side explicitly
  have hcoeff :
      coeffWin a δ 3
        =
      ![
        a 0 + a 1 * δ + a 2 * (δ ^ 2),
        a 1 + (2 : ℂ) * a 2 * δ,
        a 2
      ] :=
    by simpa using (coeffWin_eq_explicit_N3 (a := a) (δ := δ))

  -- 2️⃣ Expand transportLower side explicitly (DO NOT unfold transportLower)
  have htr :
      TAC.transportLower 3 δ (baseWinN3 a)
        =
      ![
        (baseWinN3 a) 0,
        (baseWinN3 a) 1 + δ * (baseWinN3 a) 0,
        (baseWinN3 a) 2
          + δ * (baseWinN3 a) 1
          + (δ ^ 2) / (2 : ℂ) * (baseWinN3 a) 0
      ] :=
    by simpa using
        (TAC.transportLower3_eq_stencil (δ := δ) (w := baseWinN3 a))

  -- 3️⃣ Now rewrite both sides globally before ext
  -- This prevents Lean from ever seeing transportMat/mulVec.
  calc
    coeffWin a δ 3
        = ![
            a 0 + a 1 * δ + a 2 * (δ ^ 2),
            a 1 + (2 : ℂ) * a 2 * δ,
            a 2
          ] := hcoeff
    _   =
        postWinN3
          (![
            (baseWinN3 a) 0,
            (baseWinN3 a) 1 + δ * (baseWinN3 a) 0,
            (baseWinN3 a) 2
              + δ * (baseWinN3 a) 1
              + (δ ^ 2) / (2 : ℂ) * (baseWinN3 a) 0
          ]) := by
        -- purely algebraic rewrite
        simp [postWinN3, baseWinN3, pow_two, div_eq_mul_inv,
              add_assoc, add_comm, add_left_comm,
              mul_assoc, mul_comm, mul_left_comm]
    _   =
        postWinN3 (TAC.transportLower 3 δ (baseWinN3 a)) := by
        -- IMPORTANT: avoid simp, it unfolds `transportLower` to `transportMat...mulVec`
        exact (congrArg postWinN3 htr).symm
end J3
end TAC
end XiPacket
end Targets
end Hyperlocal
