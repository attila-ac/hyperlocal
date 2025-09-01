import Hyperlocal.Cancellation.Matrix4x4
import Mathlib.Data.Complex.Basic

noncomputable section
namespace Hyperlocal
namespace Cancellation

/-- Constant weights `w i ≡ 1`. -/
def wOne : Jet4 := fun _ => (1 : ℂ)

lemma wOne_nonzero : ∀ i : Fin 4, wOne i ≠ 0 := by
  intro i; simp [wOne]

/-- Specialization of `kernel_M4_trivial` to `w ≡ 1`. -/
theorem kernel_M4_wOne (c10 c32 : ℂ) :
    ∀ x : Jet4, (M4 wOne c10 c32).mulVec x = 0 → x = 0 := by
  intro x hx
  exact kernel_M4_trivial wOne c10 c32 wOne_nonzero hx

/-- Concrete sanity: zero vector is in the kernel (and only the zero vector). -/
example : (M4 wOne (2 + 3*Complex.I) (-1)).mulVec ![0,0,0,0] = 0 := by
  -- `mulVec` with the zero vector is zero for any matrix.
  simp [M4]

end Cancellation
end Hyperlocal
end
