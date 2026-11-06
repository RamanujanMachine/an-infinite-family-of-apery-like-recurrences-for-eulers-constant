module

public import ThisWork.ReflectedDigamma

/-! Uniform digamma bounds after the saddle scaling. -/

public section

namespace ThisWork

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

theorem uniform_scaled_digamma_left {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, s.re ≤ -κ → η ≤ |s.im| →
      ‖Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)‖ ≤ (2 / κ + 4 * Real.pi) / R := by
  have ha : 0 < 2 * Real.pi * η := mul_pos (mul_pos (by norm_num) Real.pi_pos) hη
  filter_upwards [eventually_exp_decay_bounds ha] with R hdec
  obtain ⟨hR, hsmall, hinv⟩ := hdec
  refine ⟨hR, fun s hs him => ?_⟩
  have hre : ((R : ℂ) * s).re = R * s.re := by simp [Complex.mul_re]
  have hden : R * κ ≤ -((R : ℂ) * s).re := by
    rw [hre]
    have h := mul_le_mul_of_nonneg_left hs hR.le
    nlinarith
  have hneg : ((R : ℂ) * s).re < 0 := by nlinarith [mul_pos hR hκ]
  have himEq : |((R : ℂ) * s).im| = R * |s.im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos hR]
  have hexp : Real.exp (-2 * Real.pi * |((R : ℂ) * s).im|) ≤
      Real.exp (-(2 * Real.pi * η) * R) := by
    apply Real.exp_le_exp.mpr
    rw [himEq]
    have h := mul_le_mul_of_nonneg_left him hR.le
    nlinarith [mul_le_mul_of_nonneg_left h (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).le]
  have hb := norm_digamma_sub_log_left hneg (hexp.trans hsmall)
  have hfirst : 2 / (-((R : ℂ) * s).re) ≤ (2 / κ) / R :=
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos hR hκ) hden).trans_eq (by field_simp)
  have hsecond : 4 * Real.pi * Real.exp (-2 * Real.pi * |((R : ℂ) * s).im|) ≤
      4 * Real.pi * (1 / R) :=
    mul_le_mul_of_nonneg_left (hexp.trans hinv) (mul_nonneg (by norm_num) Real.pi_pos.le)
  exact (hb.trans (add_le_add hfirst hsecond)).trans_eq (by ring)

end ThisWork
