/-
  Hyperlocal/Targets/XiPacket/J3TransportStencil2_CoeffMatch_XiTransportOp2_ExplicitN3.lean

  Step 2 (deterministic, explicit form):

  Combine:
  * Step-2 canonical lemma:
      coeffWin a (delta s) 3 = postWinN3 (XiTransportOp 2 s (baseWinN3 a))
  with
  * explicit stencil for XiTransportOp 2:
      XiTransportOp₂_eq_explicit_stencil

  to rewrite everything to the same explicit length-3 window and finish by simp/ring_nf.
-/

import Hyperlocal.Targets.XiPacket.J3TransportStencil2_CoeffMatch_XiTransportOp2_N3
import Hyperlocal.Targets.XiPacket.J3TransportStencil2_XiTransportOp2_Explicit
import Hyperlocal.Targets.XiPacket.J3TransportStencil2_CoeffMatchFull

import Mathlib.Tactic

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
**Step 2 (explicit N=3):**

`coeffWin` equals the *explicit* δ-stencil window computed from `XiTransportOp 2`,
after applying the convention map `postWinN3` and using `baseWinN3`.
-/
theorem coeffWin_eq_post_XiTransportOp₂_N3_explicit
    (s : Hyperlocal.OffSeed Xi) (a : ℕ → ℂ) :
    coeffWin a (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) 3
      =
    postWinN3
      (![ (baseWinN3 a) 0,
          (baseWinN3 a) 1 + (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) * (baseWinN3 a) 0,
          (baseWinN3 a) 2
            + (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) * (baseWinN3 a) 1
            + ((((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) ^ 2) / (2 : ℂ) * (baseWinN3 a) 0 ] : Fin 3 → ℂ) := by
  classical
  have hStep2 :=
    (coeffWin_eq_post_XiTransportOp₂_N3 (s := s) (a := a))

  have hExp :
      (Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (baseWinN3 a)
        =
      (![ (baseWinN3 a) 0,
          (baseWinN3 a) 1 + (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) * (baseWinN3 a) 0,
          (baseWinN3 a) 2
            + (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) * (baseWinN3 a) 1
            + ((((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) ^ 2) / (2 : ℂ) * (baseWinN3 a) 0 ] : Fin 3 → ℂ) := by
    simpa using
      (XiTransportOp₂_eq_explicit_stencil (s := s) (w := baseWinN3 a))

  simpa [hExp] using hStep2

/--
Compute `postWinN3 (XiTransportOp 2 s (baseWinN3 a))` into the same explicit N=3 window
as `coeffWin_eq_explicit_N3`.

Key point: rewrite the `XiTransportOp` term *before* unfolding `baseWinN3`, to avoid
goals of the form `(XiTransportOp 2 s) ![...] i = ...`.
-/
theorem postWinN3_XiTransportOp₂_eq_explicit
    (s : Hyperlocal.OffSeed Xi) (a : ℕ → ℂ) :
    postWinN3 ((Hyperlocal.Targets.XiTransport.XiTransportOp 2 s) (baseWinN3 a))
      =
    (![ a 0 + a 1 * (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))
              + a 2 * ((((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) ^ 2),
        a 1 + (2 : ℂ) * a 2 * (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)),
        a 2 ] : Fin 3 → ℂ) := by
  classical

  -- Rewrite through the explicit stencil lemma INSIDE `postWinN3`.
  have h :=
    congrArg postWinN3 (XiTransportOp₂_eq_explicit_stencil (s := s) (w := baseWinN3 a))

  -- Now compute `postWinN3` of the explicit vector, coordinatewise.
  refine h.trans ?_
  ext i
  fin_cases i
  · -- slot 0: postWinN3 v 0 = v 2
    simp [postWinN3, baseWinN3, pow_two, div_eq_mul_inv,
          add_assoc, add_comm, add_left_comm,
          mul_assoc, mul_comm, mul_left_comm]
    try ring_nf
  · -- slot 1: postWinN3 v 1 = v 1
    simp [postWinN3, baseWinN3, pow_two, div_eq_mul_inv,
          add_assoc, add_comm, add_left_comm,
          mul_assoc, mul_comm, mul_left_comm]
    try ring_nf
  · -- slot 2: postWinN3 v 2 = v 0 / 2
    simp [postWinN3, baseWinN3, pow_two, div_eq_mul_inv,
          add_assoc, add_comm, add_left_comm,
          mul_assoc, mul_comm, mul_left_comm]
    try ring_nf

/--
**Step 2 final (explicit window):**

`coeffWin` equals the explicit N=3 δ-window (the same one from `coeffWin_eq_explicit_N3`),
proved by rewriting the RHS through `XiTransportOp₂`’s explicit stencil.
-/
theorem coeffWin_eq_explicit_stencil_XiTransportOp₂_N3
    (s : Hyperlocal.OffSeed Xi) (a : ℕ → ℂ) :
    coeffWin a (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) 3
      =
    (![ a 0 + a 1 * (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ))
              + a 2 * ((((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)) ^ 2),
        a 1 + (2 : ℂ) * a 2 * (((Hyperlocal.Targets.XiTransport.delta s : ℝ) : ℂ)),
        a 2 ] : Fin 3 → ℂ) := by
  classical
  exact
    (coeffWin_eq_post_XiTransportOp₂_N3 (s := s) (a := a)).trans
      (postWinN3_XiTransportOp₂_eq_explicit (s := s) (a := a))

end J3
end TAC

end XiPacket
end Targets
end Hyperlocal
