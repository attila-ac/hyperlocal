/-
  Hyperlocal/Targets/XiPacket/XiCompletedRiemannZetaBridge.lean

  Targeted bridge lemma between the regularized completion `completedRiemannZeta₀`
  and the (unregularized) completion `completedRiemannZeta`.

  This is the exact identity the Route-B anchor layer needs:

    z*(z-1)*Λ₀(z) + 1 = z*(z-1)*Λ(z)

  on the punctured domain `z ≠ 0,1`.

  Implementation note:
  We reuse the theorem-level cancellation shim already proved in
  `XiAnalyticInputs.lean` (`cancelledCompletedZeta_eq_raw`).
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

/--
Bridge lemma on the punctured domain:
`z*(z-1)*Λ₀(z) + 1 = z*(z-1)*Λ(z)`.
-/
theorem completedRiemannZeta0_bridge_of_ne (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    z * (z - 1) * completedRiemannZeta₀ z + 1
      = z * (z - 1) * completedRiemannZeta z := by
  -- `cancelledCompletedZeta_eq_raw` is stated as
  --   z*(z-1)*Λ(z) = z*(z-1)*Λ₀(z) + 1
  -- so we just flip it.
  have h := (cancelledCompletedZeta_eq_raw (w := z) h0 h1)
  -- unfold the cancellation shim
  -- cancelledCompletedZeta z = z*(z-1)*Λ₀(z) + 1
  simpa [cancelledCompletedZeta, mul_assoc] using h.symm

end XiPacket
end Targets
end Hyperlocal
