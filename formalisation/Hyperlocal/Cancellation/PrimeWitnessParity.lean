/-
  Hyperlocal/Cancellation/PrimeWitnessParity.lean

  Parity projector / odd-part scalarisation bridge.

  Goal:
    If a scalar test has the trig form
      Φ(t) = A(t) + B(t) * cos(t*L) + C(t) * sin(t*L)
    and A,B,C are even in t, then the odd-part of Φ is purely sine:
      oddPart Φ t = C(t) * sin(t*L)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Cancellation
namespace PrimeWitness

open scoped Real

/-- Odd part of a real function: (f(t) - f(-t))/2. -/
def oddPart (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - f (-t)) / 2

/-- A generic trig-shaped scalar test (t is the “phase variable”). -/
def PhiABC (A B C : ℝ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  A t + B t * Real.cos (t * L) + C t * Real.sin (t * L)

/-- Evenness predicate: f(-t)=f(t). -/
def Even (f : ℝ → ℝ) : Prop := ∀ t, f (-t) = f t

lemma oddPart_const (a : ℝ) :
    oddPart (fun _t => a) = fun _t => 0 := by
  funext t
  simp [oddPart]

lemma oddPart_cos (b L : ℝ) :
    oddPart (fun t => b * Real.cos (t * L)) = fun _ => 0 := by
  funext t
  simp [oddPart, Real.cos_neg]

lemma oddPart_sin (c L : ℝ) :
    oddPart (fun t => c * Real.sin (t * L)) = fun t => c * Real.sin (t * L) := by
  funext t
  -- oddPart = (f(t) - f(-t))/2, and sin is odd
  simp [oddPart, Real.sin_neg, sub_eq_add_neg]


/-
Main parity bridge:
If A,B,C are even-in-t, oddPart kills A and cos terms and keeps only sine.
-/
theorem oddPart_PhiABC
    {A B C : ℝ → ℝ} {L : ℝ}
    (hA : Even A) (hB : Even B) (hC : Even C) :
    ∀ t, oddPart (PhiABC A B C L) t = C t * Real.sin (t * L) := by
  intro t
  -- IMPORTANT: specialize evenness at this t so simp can rewrite A(-t),B(-t),C(-t)
  have hAt : A (-t) = A t := hA t
  have hBt : B (-t) = B t := hB t
  have hCt : C (-t) = C t := hC t
  -- Now expand oddPart(PhiABC) and simplify using trig parity
  simp [oddPart, PhiABC, hAt, hBt, hCt, Real.cos_neg, Real.sin_neg, sub_eq_add_neg]
  ring

end PrimeWitness
end Cancellation
end Hyperlocal
