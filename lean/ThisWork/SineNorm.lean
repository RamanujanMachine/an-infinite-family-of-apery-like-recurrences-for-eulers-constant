module

public import ThisWork.Argument
public import ThisWork.ReflectedDigamma

/-! Explicit logarithmic sine bounds for the Gamma reflection formula. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem norm_sin_bounds_upper {z : ℂ} (hz : Real.exp (-2 * z.im) ≤ 1 / 2) :
    Real.exp z.im / 4 ≤ ‖Complex.sin z‖ ∧ ‖Complex.sin z‖ ≤ Real.exp z.im := by
  have he : Real.exp (-z.im) ≤ Real.exp z.im / 2 := by
    have h := mul_le_mul_of_nonneg_left hz (Real.exp_pos z.im).le
    rw [← Real.exp_add, show z.im + -2 * z.im = -z.im by ring] at h
    simpa only [mul_one_div] using h
  have hnorm : ‖Complex.sin z‖ = ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2 := by
    simp [Complex.sin]
  have hlo := norm_sub_norm_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  have hup := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg] at hlo hup
  constructor <;> linarith [Real.exp_pos z.im]

theorem norm_sin_bounds {z : ℂ} (hz : Real.exp (-2 * |z.im|) ≤ 1 / 2) :
    Real.exp |z.im| / 4 ≤ ‖Complex.sin z‖ ∧ ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  by_cases him : 0 ≤ z.im
  · simpa only [abs_of_nonneg him] using norm_sin_bounds_upper (z := z) (by simpa only [abs_of_nonneg him] using hz)
  · have h := norm_sin_bounds_upper (z := -z) (by simpa only [Complex.neg_im, abs_of_neg (lt_of_not_ge him)] using hz)
    simpa only [Complex.neg_im, Complex.sin_neg, norm_neg, abs_of_neg (lt_of_not_ge him)] using h

theorem abs_log_norm_sin_sub_abs_im {z : ℂ} (hz : Real.exp (-2 * |z.im|) ≤ 1 / 2) :
    |Real.log ‖Complex.sin z‖ - abs z.im| ≤ Real.log 4 := by
  have hb := norm_sin_bounds hz
  have hpos : 0 < ‖Complex.sin z‖ :=
    (div_pos (Real.exp_pos _) (by norm_num : (0 : ℝ) < 4)).trans_le hb.1
  have hl := Real.log_le_log (div_pos (Real.exp_pos |z.im|) (by norm_num : (0 : ℝ) < 4)) hb.1
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (4 : ℝ) ≠ 0), Real.log_exp] at hl
  have hu := Real.log_le_log hpos hb.2
  rw [Real.log_exp] at hu
  exact abs_le.mpr ⟨by linarith, by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]⟩

end ThisWork.Analytic
