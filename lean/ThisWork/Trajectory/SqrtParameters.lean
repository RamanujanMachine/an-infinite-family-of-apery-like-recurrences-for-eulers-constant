module

public import ThisWork.Trajectory.SqrtPhase
public import ThisWork.SaddleApproximation

/-! Quantitative scale identities and affine-Gamma conditions for `sqrt n`. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter
open scoped Topology

theorem sqrtScale_div_nat {n : ℕ} (hn : 0 < n) :
    sqrtScale n / (n : ℝ) = 1 / sqrtScale n := by
  rw [← sqrtScale_sq n]
  field_simp [(sqrtScale_pos hn).ne']

theorem sqrtScale_div_nat_tendsto :
    Tendsto (fun n : ℕ => sqrtScale n / (n : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_inv_atTop_zero.comp sqrtScale_tendsto).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simpa only [Function.comp_apply, one_div] using (sqrtScale_div_nat hn).symm

theorem sqrtScale_le_nat {n : ℕ} (hn : 1 ≤ n) : sqrtScale n ≤ (n : ℝ) := by
  simpa only [sqrtScale, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num)

theorem inv_nat_le_inv_sqrtScale {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ 1 / sqrtScale n :=
  div_le_div_of_nonneg_left zero_le_one (sqrtScale_pos (by omega)) (sqrtScale_le_nat hn)

theorem eventually_right_factor_conditions {α : ℝ} (hα : 0 < α) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ α * n ∧ sqrtScale n * M ≤ (α * n) / 4 := by
  have hratio : Tendsto (fun n : ℕ => (sqrtScale n / (n : ℝ)) * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using sqrtScale_div_nat_tendsto.mul_const M
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (4 / α)), hratio.eventually (gt_mem_nhds (show (0 : ℝ) < α / 4 from div_pos hα (by norm_num))),
    eventually_gt_atTop (0 : ℕ)] with n hn hsmall hn0
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hα).mp hn, ?_⟩
  rw [div_mul_eq_mul_div] at hsmall
  exact ((div_lt_iff₀ (Nat.cast_pos.mpr hn0)).mp hsmall).le.trans_eq (by ring)

theorem affineError_le_inv_sqrtScale {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) (M : ℝ) :
    4 / (α * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / (α * n)) ≤
      ((11 + 3 * M) / (2 * α)) * (1 / sqrtScale n) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 4 / (α * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / (α * n)) =
      (11 / (2 * α)) * (1 / (n : ℝ)) + ((3 * M) / (2 * α)) * (sqrtScale n / (n : ℝ)) := by
    field_simp
    ring
  rw [he, sqrtScale_div_nat hn0]
  have h := add_le_add (mul_le_mul_of_nonneg_left (inv_nat_le_inv_sqrtScale hn)
    (show 0 ≤ 11 / (2 * α) by positivity)) (le_refl (((3 * M) / (2 * α)) * (1 / sqrtScale n)))
  exact h.trans_eq (by ring)

end ThisWork.Trajectory
