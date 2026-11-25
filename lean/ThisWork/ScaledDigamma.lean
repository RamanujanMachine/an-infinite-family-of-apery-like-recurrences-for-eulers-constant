module

public import ThisWork.ReflectedDigamma

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric MeasureTheory
open scoped Topology

theorem eventually_exp_decay_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ Real.exp (-a * R) ≤ 1 / 2 ∧ Real.exp (-a * R) ≤ 1 / R := by
  have h₀ := (isLittleO_exp_neg_mul_rpow_atTop ha 0).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have h₁ := (isLittleO_exp_neg_mul_rpow_atTop ha (-1)).bound zero_lt_one
  filter_upwards [h₀, h₁, eventually_gt_atTop (0 : ℝ)] with R h₀ h₁ hR
  refine ⟨hR, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_zero, abs_one, mul_one] using h₀
  · simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_neg_one,
      abs_of_pos (inv_pos.mpr hR), one_mul, one_div] using h₁

theorem uniform_scaled_digamma_right {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, κ ≤ s.re →
      ‖Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)‖ ≤ (2 / κ) / R := by
  filter_upwards [eventually_ge_atTop (2 / κ)] with R hR
  have hR0 : 0 < R := (div_pos (by norm_num) hκ).trans_le hR
  refine ⟨hR0, fun s hs => ?_⟩
  have hscale : ((R : ℂ) * s).re = R * s.re := by simp [Complex.mul_re]
  have hsmall : 2 ≤ ((R : ℂ) * s).re := by
    rw [hscale]
    exact ((div_le_iff₀ hκ).mp hR).trans (mul_le_mul_of_nonneg_left hs hR0.le)
  have h := norm_digamma_sub_log_le_two_div hsmall
  rw [hscale] at h
  exact (h.trans (div_le_div_of_nonneg_left (by norm_num) (mul_pos hR0 hκ)
    (mul_le_mul_of_nonneg_left hs hR0.le))).trans_eq (by field_simp)

end ThisWork.Analytic
