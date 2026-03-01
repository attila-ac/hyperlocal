import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Basic
open Complex

#find AnalyticAt ℂ completedRiemannZeta (?z : ℂ)

#find completedRiemannZeta ((starRingEnd ℂ) (?s : ℂ)) =
      (starRingEnd ℂ) (completedRiemannZeta (?s : ℂ))

#find completedRiemannZeta (star (?s : ℂ)) = star (completedRiemannZeta (?s : ℂ))
