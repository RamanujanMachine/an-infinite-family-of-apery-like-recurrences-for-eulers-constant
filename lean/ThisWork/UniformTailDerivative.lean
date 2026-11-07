module

public import ThisWork.Argument
public import ThisWork.SaddleContours

/-! Uniform bounds for the actual logarithmic derivative on the horizontal tails. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem norm_right_factor_tail_le {α R t y H : ℝ} {n : ℕ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hRn : R ≤ n) (hn : 1 ≤ n)
    (ht : 1 ≤ t) (hy : |y| ≤ H) :
    ‖(α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ ≤
      (n : ℝ) * (α + H + 2) * t := by
  rw [show (α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1 =
    ((α * n + R * t + 1 : ℝ) : ℂ) + ((-R * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  calc
    _ ≤ ‖((α * n + R * t + 1 : ℝ) : ℂ)‖ + ‖((-R * y : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = α * n + R * t + 1 + R * |y| := by
      rw [Complex.norm_of_nonneg (show 0 ≤ α * n + R * t + 1 by positivity)]
      simp [abs_of_nonneg hR]
    _ ≤ (n : ℝ) * (α + H + 2) * t := by
      have hH : 0 ≤ H := (abs_nonneg y).trans hy
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn,
        mul_le_mul_of_nonneg_right hRn (show 0 ≤ t by linarith),
        mul_le_mul_of_nonneg_left hy hR,
        mul_le_mul_of_nonneg_right hRn hH,
        mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (show 0 ≤ α + H + 1 by positivity))
          (show 0 ≤ t - 1 by linarith)]

theorem re_digamma_le_log_norm_add_one {z : ℂ} (hz : 2 ≤ z.re) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + 1 := by
  have h := norm_digamma_sub_log_le_two_div hz
  have hre : (Complex.digamma z).re - Real.log ‖z‖ ≤ 2 / z.re := by
    simpa only [Complex.sub_re, Complex.log_re] using (Complex.re_le_norm _).trans h
  linarith [(div_le_iff₀ (show 0 < z.re by linarith)).mpr
    (show (2 : ℝ) ≤ 1 * z.re by linarith)]

theorem re_digamma_right_tail_le {α R t y H : ℝ} {n : ℕ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hRn : R ≤ n) (hn : 1 ≤ n)
    (ht : 1 ≤ t) (hy : |y| ≤ H) (hA : 4 ≤ α * n) :
    (Complex.digamma ((α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1)).re ≤
      Real.log (n : ℝ) + Real.log (α + H + 2) + Real.log t + 1 := by
  have hz : 2 ≤ ((α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, Complex.neg_re,
      Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
    nlinarith [mul_nonneg hR (show 0 ≤ t by linarith)]
  have hl := Real.log_le_log
    (show 0 < ‖(α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ from
      (show (0 : ℝ) < 2 by norm_num).trans_le (hz.trans (Complex.re_le_norm _)))
    (norm_right_factor_tail_le hα hR hRn hn ht hy)
  have hH : 0 ≤ H := (abs_nonneg y).trans hy
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul (mul_pos hn₀ (show 0 < α + H + 2 by positivity)).ne'
    (show t ≠ 0 by linarith), Real.log_mul hn₀.ne' (show α + H + 2 ≠ 0 by positivity)] at hl
  linarith [re_digamma_le_log_norm_add_one hz]

theorem re_digamma_left_tail_ge {R t y D : ℝ} (hR : 1 ≤ R) (ht : 1 ≤ t)
    (hb : ‖Complex.digamma ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.log ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤ D) :
    Real.log R + Real.log t - D ≤
      (Complex.digamma ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))).re := by
  have hn : R * t ≤ ‖(R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ := by
    have h := Complex.abs_re_le_norm ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))
    simpa [Complex.mul_re, abs_of_nonneg (show 0 ≤ R by linarith),
      abs_of_nonneg (show 0 ≤ t by linarith)] using h
  have hl := Real.log_le_log (mul_pos (show 0 < R by linarith) (show 0 < t by linarith)) hn
  have he : |(Complex.digamma ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))).re -
      Real.log ‖(R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖| ≤ D := by
    simpa only [Complex.sub_re, Complex.log_re] using (Complex.abs_re_le_norm _).trans hb
  linarith [(abs_le.mp he).1, Real.log_mul (show R ≠ 0 by linarith) (show t ≠ 0 by linarith)]

/-- The exact logarithmic derivative grows at least logarithmically toward
the far left, with a constant and index threshold uniform along both tails. -/
theorem uniform_re_exactSaddleEquation_left_lower [PositiveArgument] {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log t - C ≤ (exactSaddleEquation α₁ α₂ j n (-(t : ℂ) + (y : ℂ) * Complex.I)).re := by
  refine ⟨max 0 (Real.log (α₁ + H + 2) + Real.log (α₂ + H + 2) +
    3 * (2 + 4 * Real.pi) + 2 + |Real.log PositiveArgument.value|), le_max_left _ _, ?_⟩
  filter_upwards [largeScale_tendsto.eventually (uniform_scaled_digamma_left zero_lt_one hη),
    eventually_right_factor_conditions h₁ 0, eventually_right_factor_conditions h₂ 0,
    largeScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with n hψ hA₁ hA₂ hR hn t ht y hy hyH
  have hRn : largeScale n ≤ (n : ℝ) :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hb : ‖Complex.digamma ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.log ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤ 2 + 4 * Real.pi := by
    have h := hψ.2 (-(t : ℂ) + (y : ℂ) * Complex.I) (by simpa using neg_le_neg ht) (by simpa using hy)
    exact h.trans (by simpa only [div_one] using div_le_self (by positivity : 0 ≤ 2 + 4 * Real.pi) hR)
  simp only [exactSaddleEquation, kernelLogDerivative, kernelTwist, Complex.ofReal_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, twist_re]
  linarith [le_abs_self (Real.log PositiveArgument.value), re_digamma_left_tail_ge hR ht hb,
    re_digamma_right_tail_le h₁.le hψ.1.le hRn hn ht hyH hA₁.1,
    re_digamma_right_tail_le h₂.le hψ.1.le hRn hn ht hyH hA₂.1,
    log_largeScale (show 0 < n by omega),
    le_max_right 0 (Real.log (α₁ + H + 2) + Real.log (α₂ + H + 2) + 3 * (2 + 4 * Real.pi) + 2 + |Real.log PositiveArgument.value|)]

end ThisWork.Analytic
