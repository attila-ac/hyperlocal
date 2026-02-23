import Hyperlocal.Targets.XiPacket.TACTransportTruncated_Finite
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

/-- iterated complex derivative -/
def cderivIter (m : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (deriv^[m] f)

/-- jet vector -/
def jetVec (N : ℕ) (f : ℂ → ℂ) (z : ℂ) : Fin N → ℂ :=
  fun j => cderivIter (j : ℕ) f z

/--
Jet version of the finite transport expansion.

This is still the “truncated Taylor stencil”, just presented as a filtered sum.
-/
theorem transport_apply_eq_filterSum_jet
    (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) (j : Fin N) :
    transport N δ (jetVec N f z) j
      =
    ((Finset.univ.filter (fun m : Fin N => j ≤ m)).sum (fun m : Fin N =>
        (δ ^ ((m : ℕ) - (j : ℕ))) /
            (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
          * cderivIter (m : ℕ) f z)) := by
  classical
  simpa [jetVec] using
    (transport_apply_eq_filterSum (N := N) (Γ := jetVec N f z) (δ := δ) (j := j))

end TAC
end XiPacket
end Targets
end Hyperlocal
