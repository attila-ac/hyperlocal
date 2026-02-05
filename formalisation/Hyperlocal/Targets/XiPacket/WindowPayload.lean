/-
  Hyperlocal/Targets/XiPacket/WindowPayload.lean

  Semantic payload (the “last cliff” object):

  • complex windows w0 wc ws wp2 wp3 : Window 3
  • prime decompositions written *pointwise at window level*
  • determinant facts already stated after vectorization (ell/kappa on ℝ³)

  Design choice:
  We vectorize via `reVec3`. If your ξ-window extraction naturally lives in the
  imaginary lane instead, you can swap to an `imVec3` variant later (you’d add
  `imVec3` + simp lemmas analogously in `Vectorize.lean` and change the three
  determinant fields accordingly).
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Minimal ξ-window payload at parameters (σ,t).

This is the object your Toeplitz/window recurrence should *produce*.
Everything downstream is purely algebraic packaging.
-/
structure WindowPayload (σ t : ℝ) : Type where
  w0  : Transport.Window 3
  wc  : Transport.Window 3
  ws  : Transport.Window 3
  wp2 : Transport.Window 3
  wp3 : Transport.Window 3

  /- Prime decompositions at window level (stored pointwise to avoid Pi-type
     typeclass elaboration issues). -/
  hw2 :
    ∀ i : Fin 3,
      wp2 i = w0 i
        + ( (aCoeff σ t (2 : ℝ) : ℂ) * (wc i) )
        + ( (bCoeff σ t (2 : ℝ) : ℂ) * (ws i) )

  hw3 :
    ∀ i : Fin 3,
      wp3 i = w0 i
        + ( (aCoeff σ t (3 : ℝ) : ℂ) * (wc i) )
        + ( (bCoeff σ t (3 : ℝ) : ℂ) * (ws i) )

  /- Determinant facts stated already on the real vectors after vectorization. -/
  hell2 : Transport.ell (reVec3 w0) (reVec3 wc) (reVec3 wp2) = 0
  hell3 : Transport.ell (reVec3 w0) (reVec3 wc) (reVec3 wp3) = 0
  hkappa : Transport.kappa (reVec3 w0) (reVec3 wc) (reVec3 ws) ≠ 0

end XiPacket
end Targets
end Hyperlocal
