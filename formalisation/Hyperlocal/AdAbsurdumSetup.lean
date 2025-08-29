import Hyperlocal.Core

namespace Hyperlocal

structure OffSeed (H : ℂ → ℂ) where
  ρ  : ℂ
  hρ : H ρ = 0
  hσ : ρ.re ≠ (1 : ℝ) / 2
  ht : ρ.im ≠ 0


theorem seed_gives_quartet
    (H  : ℂ → ℂ)
    (FE : ∀ s : ℂ, H s = H (oneMinus s))
    (RC : ∀ s : ℂ, H (star s) = star (H s))
    (s  : OffSeed H) :
    H s.ρ = 0 ∧ H (star s.ρ) = 0 ∧ H (oneMinus s.ρ) = 0 ∧
      H (oneMinus (star s.ρ)) = 0 :=
  zero_quartet H FE RC (ρ := s.ρ) s.hρ

end Hyperlocal
