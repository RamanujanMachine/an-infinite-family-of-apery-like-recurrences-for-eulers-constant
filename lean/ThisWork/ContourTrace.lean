module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import ThisWork.ComplexLogTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology

/-- Lower horizontal ray, right vertical edge, and upper horizontal ray. -/
def hankelTrace (right height : ℝ) : Set ℂ :=
  {s | ∃ x ≤ right, s = (x : ℂ) + (-height : ℝ) * Complex.I} ∪
  {s | ∃ y ∈ Icc (-height) height, s = (right : ℂ) + (y : ℂ) * Complex.I} ∪
  {s | ∃ x ≤ right, s = (x : ℂ) + (height : ℂ) * Complex.I}

theorem hankelTrace_mem_slitPlane {right height : ℝ} (hr : 0 < right) (hh : 0 < height)
    {s : ℂ} (hs : s ∈ hankelTrace right height) : s ∈ Complex.slitPlane := by
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using neg_ne_zero.mpr hh.ne'
  · apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using hr
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using hh.ne'

theorem hankelTrace_re_le {right height : ℝ} {s : ℂ} (hs : s ∈ hankelTrace right height) :
    s.re ≤ right := by
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · simpa using hx
  · simp
  · simpa using hx

end ThisWork.Analytic
