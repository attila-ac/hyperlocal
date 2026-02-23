/-
  Hyperlocal/Targets/XiPacket/J3TransportStencil2_CoeffMatch_XiTransportOp2_N3.lean

  Step 2 (deterministic, cycle-safe): connect the Step-1 `N=3` coefficient extraction
  convention to the *concrete* transport operator `XiTransportOp 2`.

  Core lemma:

    coeffWin a (delta s) 3 = postWinN3 (XiTransportOp 2 s (baseWinN3 a))

  so downstream proofs can rewrite both sides to the same explicit δ-stencil and
  finish by `simp` / `ring_nf`.
-/

import Hyperlocal.Targets.XiPacket.J3TransportStencil2_CoeffMatchTransport_N3
import Hyperlocal.Targets.XiPacket.J3TransportStencil2_XiTransportOp2_Explicit

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC
namespace J3

open Hyperlocal.Targets.XiTransport

/--
**Step 2 (N=3):** `J3` coefficient extraction matches the concrete `XiTransportOp 2`
(after applying the fixed convention map `postWinN3` and using `baseWinN3`).

This is the canonical Step-2 lemma used downstream.
-/
theorem coeffWin_eq_post_XiTransportOp₂_N3
    (s : Hyperlocal.OffSeed Xi) (a : ℕ → ℂ) :
    coeffWin a (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) 3
      =
    postWinN3 ((Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (baseWinN3 a)) := by
  classical

  -- Step 1 gives the result against `transportLower`.
  have h1 :=
    (coeffWin_eq_post_transportLower_N3
      (a := a)
      (δ := (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))))

  -- Compatibility identifies `XiTransportOp 2` with `transportLower 3`.
  have hcompat :=
    (TAC.XiTransportOp₂_eq_transportLower
      (s := s)
      (w := baseWinN3 a))

  -- Push through the convention map.
  have hpost :
      postWinN3 (TAC.transportLower 3 (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) (baseWinN3 a))
        =
      postWinN3 ((Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (baseWinN3 a)) := by
    -- `hcompat` has `XiTransportOp` on the left; we want `transportLower` on the left.
    have := (congrArg postWinN3 hcompat).symm
    -- Remove any eta-expansion introduced by the compatibility lemma.
    simpa using this

  -- Combine Step 1 + compat.
  exact h1.trans hpost

/-
Alternative proof (same statement), kept as a second “solution”:

Instead of building a separate `hpost`, we let `simp` rewrite the RHS through the
compatibility lemma inside `postWinN3`.
-/
theorem coeffWin_eq_post_XiTransportOp₂_N3_simp
    (s : Hyperlocal.OffSeed Xi) (a : ℕ → ℂ) :
    coeffWin a (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) 3
      =
    postWinN3 ((Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (baseWinN3 a)) := by
  classical
  -- Start from the Step-1 transportLower statement and rewrite the RHS by compat.
  simpa
    [TAC.XiTransportOp₂_eq_transportLower (s := s) (w := baseWinN3 a)]
    using
      (coeffWin_eq_post_transportLower_N3
        (a := a)
        (δ := (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))))

end J3
end TAC

end XiPacket
end Targets
end Hyperlocal
