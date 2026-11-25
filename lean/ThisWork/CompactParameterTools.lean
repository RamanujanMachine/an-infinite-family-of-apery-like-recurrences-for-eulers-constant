module

public import ThisWork.TaylorTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology OnePoint

/-- Discard a finite initial segment while retaining the compact parameter space. -/
noncomputable def parameterShift (N : ℕ) : C(OnePoint ℕ, OnePoint ℕ) :=
  OnePoint.continuousMapMkNat (fun m => ((m + N : ℕ) : OnePoint ℕ)) ∞
    (((OnePoint.continuous_iff_from_nat (id : OnePoint ℕ → OnePoint ℕ)).mp continuous_id).comp
      (tendsto_add_atTop_nat N))

@[simp] theorem parameterShift_nat (N m : ℕ) : parameterShift N m = ((m + N : ℕ) : OnePoint ℕ) := rfl

end ThisWork.Analytic
