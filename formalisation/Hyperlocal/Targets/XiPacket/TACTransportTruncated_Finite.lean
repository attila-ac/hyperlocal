/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_Finite.lean

  Snapshot-robust finite expansion lemma for TAC transport:
  we stop at the filtered-sum ("upper-triangular") form, without reindexing to `range (N-j)`.

  IMPORTANT: We do NOT rely on `Matrix.dotProduct` being named in Mathlib.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open scoped BigOperators

/--
Purely finite Toeplitz transport expansion (snapshot-robust):

For arbitrary vector `Γ`, the transported value at index `j` is a filtered sum
over `m : Fin N` with the guard `j ≤ m`.

This is the *upper-triangular stencil* form, but without reindexing to `range (N-j)`
(which is the snapshot-fragile part).
-/
theorem transport_apply_eq_filterSum
    (N : ℕ) (Γ : Fin N → ℂ) (δ : ℂ) (j : Fin N) :
    transport N δ Γ j
      =
    ((Finset.univ.filter (fun m : Fin N => j ≤ m)).sum (fun m : Fin N =>
        (δ ^ ((m : ℕ) - (j : ℕ))) /
            (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
          * Γ m)) := by
  classical

  -- Unfold transport. In this snapshot, this leaves a dot-product `⬝ᵥ`.
  simp [TAC.transport, TAC.transportMat, Matrix.mulVec]

  /-
    At this point the goal is (up to definitional equality):
      (fun m => if j ≤ m then δ^(m-j)/fact(m-j) else 0) ⬝ᵥ Γ
        = (filter ...).sum (fun m => δ^(m-j)/fact(m-j) * Γ m)

    We avoid `Matrix.dotProduct` (missing in snapshot) by unfolding `⬝ᵥ` directly.
    The notation `⬝ᵥ` is definitional as a `Finset.univ.sum`, so `simp [Matrix.vecMul]`
    is unnecessary; we just `change` to the sum form and proceed.
  -/

  -- Unfold `⬝ᵥ` by hand: it is `Finset.univ.sum (fun m => row m * vec m)`.
  -- We do this with `change` + `simp` using the definitional equation for `⬝ᵥ`.
  --
  -- The following `change` is robust because it only mentions `Finset.univ.sum`,
  -- which exists in every snapshot.
  change
      (Finset.univ.sum fun m : Fin N =>
        (if j ≤ m then
            (δ ^ ((m : ℕ) - (j : ℕ))) /
              (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
          else 0) * Γ m)
    =
      ((Finset.univ.filter (fun m : Fin N => j ≤ m)).sum fun m : Fin N =>
        (δ ^ ((m : ℕ) - (j : ℕ))) /
          (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
          * Γ m)

  -- Now it is exactly the standard `sum_filter` reshaping.
  -- `Finset.sum_filter`:
  --   (s.filter p).sum f = s.sum (fun x => if p x then f x else 0)
  -- so we use `.symm`.
  simpa using
    (Finset.sum_filter
      (s := (Finset.univ : Finset (Fin N)))
      (p := fun m : Fin N => j ≤ m)
      (f := fun m : Fin N =>
        (δ ^ ((m : ℕ) - (j : ℕ))) /
          (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
          * Γ m)
    ).symm

end TAC
end XiPacket
end Targets
end Hyperlocal
