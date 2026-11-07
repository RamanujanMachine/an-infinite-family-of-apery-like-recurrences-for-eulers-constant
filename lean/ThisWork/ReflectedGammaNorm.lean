module

public import ThisWork.Argument
public import ThisWork.GammaNorm
public import ThisWork.SineNorm

/-! Logarithmic Gamma bounds in the reflected saddle sectors. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem stirlingMain_reflection_re {z : ℂ} (hz : z.im ≠ 0) :
    (stirlingMain z).re + (stirlingMain (-z)).re = -Real.pi * |z.im| := by
  by_cases hi : 0 < z.im
  · simp [stirlingMain, log_neg_of_im_pos hi, Complex.mul_re, Complex.mul_im, abs_of_pos hi]
    ring
  · have hn : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hi) hz
    simp [stirlingMain, log_neg_of_im_neg hn, Complex.mul_re, Complex.mul_im, abs_of_neg hn]
    ring

theorem gammaNormError_reflection {z : ℂ} (hre : z.re < 0) (him : z.im ≠ 0) :
    gammaNormError z + gammaNormError (-z) = Real.log Real.pi - Real.log ‖z‖ -
      Real.log ‖Complex.sin ((Real.pi : ℂ) * z)‖ + Real.pi * |z.im| := by
  have hz : z ≠ 0 := fun h => him (by simp only [h, Complex.zero_im])
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero
    (not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inr him)))
  have hΓneg : Complex.Gamma (-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa only [Complex.neg_re] using neg_pos.mpr hre)
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [show 1 - z = -z + 1 by ring, Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)] at h
  have hs : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at h
    exact mul_ne_zero hΓ (mul_ne_zero (neg_ne_zero.mpr hz) hΓneg) h
  have hn := congrArg norm h
  rw [norm_mul, norm_mul, norm_neg, norm_div, Complex.norm_of_nonneg Real.pi_pos.le] at hn
  have hl := congrArg Real.log hn
  rw [Real.log_mul (norm_ne_zero_iff.mpr hΓ)
    (mul_ne_zero (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hΓneg)),
    Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hΓneg),
    Real.log_div Real.pi_ne_zero (norm_ne_zero_iff.mpr hs)] at hl
  dsimp only [gammaNormError]
  linarith [stirlingMain_reflection_re him]

/-- A reflected-sector Stirling bound with an explicit logarithmic error. -/
theorem abs_gammaNormError_left {z : ℂ} (hre : z.re ≤ -2)
    (hexp : Real.exp (-2 * Real.pi * |z.im|) ≤ 1 / 2) :
    |gammaNormError z| ≤ (|gammaNormError 2| + |Real.log Real.pi| + Real.log 4) +
      3 * Real.log ‖z‖ + 2 * |z.im| / (-z.re) := by
  have him : z.im ≠ 0 := by
    intro him
    norm_num [him] at hexp
  have hπim : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]
  have hs := abs_log_norm_sin_sub_abs_im (z := (Real.pi : ℂ) * z)
    (by simpa only [hπim, mul_assoc] using hexp)
  rw [hπim] at hs
  have hnorm : -z.re ≤ ‖z‖ := by
    simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm (-z)
  have hlog := Real.log_le_log (show 0 < -z.re by linarith) hnorm
  have hright := abs_gammaNormError_right (z := -z) (by simpa only [Complex.neg_re] using (show 2 ≤ -z.re by linarith))
  simp only [Complex.neg_re, Complex.neg_im, abs_neg] at hright
  have href := gammaNormError_reflection (show z.re < 0 by linarith) him
  obtain ⟨hr₀, hr₁⟩ := abs_le.mp hright
  obtain ⟨hs₀, hs₁⟩ := abs_le.mp hs
  have hnlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  exact abs_le.mpr ⟨by linarith [neg_le_abs (Real.log Real.pi)],
    by linarith [le_abs_self (Real.log Real.pi)]⟩

end ThisWork.Analytic
