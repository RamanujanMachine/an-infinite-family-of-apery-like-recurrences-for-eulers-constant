module

public import Neuschel.LocalExpansion
public import ThisWork.PrimitiveTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology OnePoint

theorem hasSum_quadratic_of_analytic {p : ℂ → ℂ} (hp : AnalyticAt ℂ p 0)
    (hp0 : p 0 = 0) (hp1 : deriv p 0 = 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => (iteratedDeriv (n + 2) p 0 / ((n + 2).factorial : ℂ)) * t ^ (2 + n)) (p t) := by
  have hs := hasFPowerSeriesAt_iff'.mp hp.hasFPowerSeriesAt
  filter_upwards [hs] with t ht
  simpa [FormalMultilinearSeries.coeff_ofScalars, Finset.sum_range_succ,
    iteratedDeriv_zero, iteratedDeriv_one, hp0, hp1, smul_eq_mul,
    Nat.add_comm, mul_comm] using (hasSum_nat_add_iff' 2).mpr ht

end ThisWork.Analytic
