module

public import ThisWork.Argument
public import ThisWork.DigammaBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! Digamma estimates in the reflected sectors containing the complex saddles. -/

public section

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

theorem norm_digamma_sub_log_left_upper {s : ℂ} (hre : s.re < 0) (him : 0 < s.im)
    (hexp : Real.exp (-2 * Real.pi * s.im) ≤ 1 / 2) :
    ‖Complex.digamma s - Complex.log s‖ ≤
      2 / (-s.re) + 4 * Real.pi * Real.exp (-2 * Real.pi * s.im) := by
  let A := Complex.digamma (1 - s) - Complex.log (1 - s)
  let B := Complex.log (1 - s) - Complex.log (-s)
  let C := Complex.cot ((Real.pi : ℂ) * s) + Complex.I
  have hA : ‖A‖ ≤ 1 / (-s.re) := by
    have h := norm_digamma_sub_log_le (s := 1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    simpa only [Complex.sub_re, Complex.one_re, sub_sub_cancel_left] using h
  have hB : ‖B‖ ≤ 1 / (-s.re) := by
    have h := norm_log_add_one_sub_le (s := -s) (by simp only [Complex.neg_re]; linarith)
    simpa only [Complex.neg_re, neg_add_eq_sub] using h
  have hC : ‖C‖ ≤ 4 * Real.exp (-2 * Real.pi * s.im) := norm_cot_pi_add_I_le hexp
  have he : Complex.digamma s - Complex.log s = A + B - (Real.pi : ℂ) * C := by
    dsimp [A, B, C]
    rw [digamma_reflection_of_im_ne_zero him.ne', log_neg_of_im_pos him]
    ring
  rw [he]
  have ht := (norm_sub_le (A + B) ((Real.pi : ℂ) * C)).trans
    (add_le_add (norm_add_le A B) le_rfl)
  rw [norm_mul, Complex.norm_of_nonneg Real.pi_pos.le] at ht
  exact (ht.trans (add_le_add (add_le_add hA hB)
    (mul_le_mul_of_nonneg_left hC Real.pi_pos.le))).trans_eq (by ring)

theorem norm_digamma_sub_log_left_lower {s : ℂ} (hre : s.re < 0) (him : s.im < 0)
    (hexp : Real.exp (2 * Real.pi * s.im) ≤ 1 / 2) :
    ‖Complex.digamma s - Complex.log s‖ ≤
      2 / (-s.re) + 4 * Real.pi * Real.exp (2 * Real.pi * s.im) := by
  let A := Complex.digamma (1 - s) - Complex.log (1 - s)
  let B := Complex.log (1 - s) - Complex.log (-s)
  let C := Complex.cot ((Real.pi : ℂ) * s) - Complex.I
  have hA : ‖A‖ ≤ 1 / (-s.re) := by
    have h := norm_digamma_sub_log_le (s := 1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    simpa only [Complex.sub_re, Complex.one_re, sub_sub_cancel_left] using h
  have hB : ‖B‖ ≤ 1 / (-s.re) := by
    have h := norm_log_add_one_sub_le (s := -s) (by simp only [Complex.neg_re]; linarith)
    simpa only [Complex.neg_re, neg_add_eq_sub] using h
  have hC : ‖C‖ ≤ 4 * Real.exp (2 * Real.pi * s.im) := norm_cot_pi_sub_I_le hexp
  have he : Complex.digamma s - Complex.log s = A + B - (Real.pi : ℂ) * C := by
    dsimp [A, B, C]
    rw [digamma_reflection_of_im_ne_zero him.ne, log_neg_of_im_neg him]
    ring
  rw [he]
  have ht := (norm_sub_le (A + B) ((Real.pi : ℂ) * C)).trans
    (add_le_add (norm_add_le A B) le_rfl)
  rw [norm_mul, Complex.norm_of_nonneg Real.pi_pos.le] at ht
  exact (ht.trans (add_le_add (add_le_add hA hB)
    (mul_le_mul_of_nonneg_left hC Real.pi_pos.le))).trans_eq (by ring)

theorem norm_digamma_sub_log_left {s : ℂ} (hre : s.re < 0)
    (hexp : Real.exp (-2 * Real.pi * |s.im|) ≤ 1 / 2) :
    ‖Complex.digamma s - Complex.log s‖ ≤
      2 / (-s.re) + 4 * Real.pi * Real.exp (-2 * Real.pi * |s.im|) := by
  have himne : s.im ≠ 0 := by
    intro he
    rw [he, abs_zero, mul_zero, Real.exp_zero] at hexp
    norm_num at hexp
  rcases lt_or_gt_of_ne himne with him | him
  · have he : -2 * Real.pi * |s.im| = 2 * Real.pi * s.im := by
      rw [abs_of_neg him]
      ring
    rw [he] at hexp ⊢
    exact norm_digamma_sub_log_left_lower hre him hexp
  · rw [abs_of_pos him] at hexp ⊢
    exact norm_digamma_sub_log_left_upper hre him hexp

end ThisWork.Analytic
