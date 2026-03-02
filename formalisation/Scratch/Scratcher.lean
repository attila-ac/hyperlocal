import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
open Complex
private abbrev conjEnd : ℂ →+* ℂ := starRingEnd ℂ

#check HurwitzZeta.completedHurwitzZetaEven₀

#find HurwitzZeta.completedHurwitzZetaEven₀ (0:UnitAddCircle) (conjEnd _) =
      conjEnd (HurwitzZeta.completedHurwitzZetaEven₀ (0:UnitAddCircle) _)

#find HurwitzZeta.completedHurwitzZetaEven₀ (0:UnitAddCircle) (star _) =
      star (HurwitzZeta.completedHurwitzZetaEven₀ (0:UnitAddCircle) _)

#find HurwitzZeta.completedHurwitzZetaEven₀ (0:UnitAddCircle) (IsROrC.conj _) =
      IsROrC.conj (HurwitzZeta.completedHurwitzZetaEven₀ (0:UnitAddCircle) _)
