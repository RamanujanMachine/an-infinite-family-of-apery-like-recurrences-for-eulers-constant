module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import ThisWork.DigammaBound

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric MeasureTheory
open scoped Topology

theorem log_neg_of_im_pos {s : ℂ} (hs : 0 < s.im) :
    Complex.log (-s) = Complex.log s - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, Complex.mul_re]
  · simpa [Complex.log_im, Complex.mul_im] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hs

theorem log_neg_of_im_neg {s : ℂ} (hs : s.im < 0) :
    Complex.log (-s) = Complex.log s + (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, Complex.mul_re]
  · simpa [Complex.log_im, Complex.mul_im] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hs

theorem norm_cot_add_I_le {z : ℂ} (hz : ‖Complex.exp (2 * Complex.I * z)‖ ≤ 1 / 2) :
    ‖Complex.cot z + Complex.I‖ ≤ 4 * ‖Complex.exp (2 * Complex.I * z)‖ := by
  let q := Complex.exp (2 * Complex.I * z)
  change ‖q‖ ≤ 1 / 2 at hz
  have hq : 1 - q ≠ 0 := by
    intro he
    have heq : q = 1 := (sub_eq_zero.mp he).symm
    have hbad : (1 : ℝ) ≤ 1 / 2 := by simpa only [heq, norm_one] using hz
    norm_num at hbad
  have heq : Complex.cot z + Complex.I = -2 * Complex.I * q / (1 - q) := by
    rw [Complex.cot_eq_exp_ratio]
    change (q + 1) / (Complex.I * (1 - q)) + Complex.I = _
    rw [mul_comm Complex.I (1 - q), div_mul_eq_div_div, Complex.div_I]
    field_simp
    ring
  have hden : 1 / 2 ≤ ‖1 - q‖ := by
    have h := norm_sub_norm_le (1 : ℂ) q
    simp only [norm_one] at h
    linarith
  have hnum : ‖-2 * Complex.I * q‖ = 2 * ‖q‖ := by simp
  change _ ≤ 4 * ‖q‖
  rw [heq, norm_div, hnum]
  calc
    2 * ‖q‖ / ‖1 - q‖ ≤ 2 * ‖q‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = 4 * ‖q‖ := by ring

theorem cot_neg (z : ℂ) : Complex.cot (-z) = -Complex.cot z := by
  simp [Complex.cot, div_neg_eq_neg_div]

theorem norm_cot_sub_I_le {z : ℂ} (hz : ‖Complex.exp (2 * Complex.I * (-z))‖ ≤ 1 / 2) :
    ‖Complex.cot z - Complex.I‖ ≤ 4 * ‖Complex.exp (2 * Complex.I * (-z))‖ := by
  have h := norm_cot_add_I_le hz
  have he : Complex.cot (-z) + Complex.I = -(Complex.cot z - Complex.I) := by
    rw [cot_neg]
    ring
  simpa only [he, norm_neg] using h

theorem norm_cot_exp_factor (s : ℂ) :
    ‖Complex.exp (2 * Complex.I * ((Real.pi : ℂ) * s))‖ = Real.exp (-2 * Real.pi * s.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem norm_cot_pi_add_I_le {s : ℂ} (hs : Real.exp (-2 * Real.pi * s.im) ≤ 1 / 2) :
    ‖Complex.cot ((Real.pi : ℂ) * s) + Complex.I‖ ≤ 4 * Real.exp (-2 * Real.pi * s.im) := by
  have h := norm_cot_add_I_le (z := (Real.pi : ℂ) * s) (by rw [norm_cot_exp_factor]; exact hs)
  simpa only [norm_cot_exp_factor] using h

theorem norm_cot_pi_sub_I_le {s : ℂ} (hs : Real.exp (2 * Real.pi * s.im) ≤ 1 / 2) :
    ‖Complex.cot ((Real.pi : ℂ) * s) - Complex.I‖ ≤ 4 * Real.exp (2 * Real.pi * s.im) := by
  have hfactor : ‖Complex.exp (2 * Complex.I * (-((Real.pi : ℂ) * s)))‖ =
      Real.exp (2 * Real.pi * s.im) := by
    rw [← mul_neg, norm_cot_exp_factor]
    congr 1
    simp only [Complex.neg_im]
    ring
  have h := norm_cot_sub_I_le (z := (Real.pi : ℂ) * s) (by rw [hfactor]; exact hs)
  simpa only [hfactor] using h

theorem digamma_reflection_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.digamma (1 - s) = Complex.digamma s + (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * s) := by
  apply Complex.digamma_one_sub
  intro m he
  apply hs
  simp only [he, Complex.intCast_im]

end ThisWork.Analytic
