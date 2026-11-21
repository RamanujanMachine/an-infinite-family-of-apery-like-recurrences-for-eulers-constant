module
public import ThisWork.Trajectory.SqrtPhase
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Logarithmic errors are negligible on the square-root exponential scale. -/
public section
namespace ThisWork.Trajectory
open Filter
open scoped Topology

theorem eventually_const_log_sqrt_le (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (1 + Real.log (sqrtScale n)) ≤ ε * sqrtScale n := by
  have hlog : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi := tendsto_inv_atTop_zero.comp sqrtScale_tendsto
  have hlim : Tendsto (fun n => C * (1 + Real.log (sqrtScale n)) / sqrtScale n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, div_eq_mul_inv, mul_add, add_mul, one_mul, mul_one,
      mul_assoc, Function.comp_def] using (hi.add (hlog.comp sqrtScale_tendsto)).const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  exact ((div_lt_iff₀ (sqrtScale_pos hn₀)).mp hn).le

end ThisWork.Trajectory
