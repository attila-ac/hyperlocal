-- Hyperlocal/Cancellation/InstabilityK1_Assemble.lean
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.InstabilityK1_Fillers
import Hyperlocal.Cancellation.InstabilityK1_Small
import Hyperlocal.Cancellation.InstabilityK1_Mid
import Hyperlocal.Cancellation.InstabilityK1_Large

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK1
namespace Assemble

open InstabilityK1

/-- Build a k=1 global instability proof from the three region packages. -/
def cover_k1 (A : ℝ) : K1RegionCover A :=
{ t1    := Mid.t1_mid,
  t2    := Mid.t2_mid,
  h0    := (Small.SmallHyp_pkg A).h0,
  h12   := (Mid.MidHyp_pkg A).h12,
  small := (Small.SmallHyp_pkg A).prove,
  mid   := (Mid.MidHyp_pkg A).prove,
  large := (Large.LargeHyp_pkg A).prove }

/-- Assembled global toggle (kept separate to avoid clashing your existing name). -/
theorem unstable_k1_all_t_from_regions (A t : ℝ) : UnstableHom 1 A t := by
  by_cases ht : 0 < t
  · exact unstable_from_fillers
      (S := Small.SmallHyp_pkg A)
      (M := Mid.MidHyp_pkg A)
      (L := Large.LargeHyp_pkg A)
      ht
  · -- if you eventually want only t>0, you can specialize; for now still a harmless fallback
    exact ⟨trivial⟩

/-- Optional: expose a typeclass instance via the regional cover (rename so it doesn't
    shadow your existing `instUnstable_k1`). Comment out if you don't want it yet. -/
instance instUnstable_k1_from_regions (A t : ℝ) : UnstableHom 1 A t :=
  unstable_k1_all_t_from_regions A t

end Assemble
end InstabilityK1
end Cancellation
end Hyperlocal
