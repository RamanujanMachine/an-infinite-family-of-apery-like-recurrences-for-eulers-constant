module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import ThisWork.ContourDefinitions
public import ThisWork.ContourTrace

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology

theorem not_neg_nat_of_mem_slitPlane {x : ℂ} (hx : x ∈ Complex.slitPlane) (m : ℕ) :
    x ≠ -(m : ℂ) := by
  rintro rfl
  simp [Complex.mem_slitPlane_iff] at hx
  exact not_lt_of_ge (Nat.cast_nonneg m) hx

end ThisWork.Analytic
