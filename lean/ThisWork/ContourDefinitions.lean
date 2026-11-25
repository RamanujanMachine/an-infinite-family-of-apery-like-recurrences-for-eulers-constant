module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ThisWork.ComplexLogTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

/-- Positively oriented left Hankel contour, shared by all defining integrals. -/
noncomputable def hankelIntegral (right height : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ u in Iic right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
    (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
    ∫ u in Iic right, f ((u : ℂ) + (height : ℂ) * Complex.I)

end ThisWork
