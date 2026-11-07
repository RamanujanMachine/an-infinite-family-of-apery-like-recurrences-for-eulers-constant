module

public import ThisWork.Argument
public import ThisWork.GammaTailBounds

/-! Decay on horizontal Mellin–Barnes tails and absolute convergence. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory
open scoped Topology

theorem log_norm_sine_tail_lower {z : ℂ} (hz : 1 ≤ |z.im|) :
    -Real.log 4 ≤ Real.log ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have him : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]
  have hs := abs_log_norm_sin_sub_abs_im (z := (Real.pi : ℂ) * z)
    (by simpa only [him, mul_assoc] using sine_tail_exp_bound hz)
  rw [him] at hs
  nlinarith [(abs_le.mp hs).1, mul_nonneg Real.pi_pos.le (abs_nonneg z.im)]

theorem twist_re_le (j : Branch) {z : ℂ} {H : ℝ} (hz : |z.im| ≤ H) :
    (twist j * z).re ≤ 2 * Real.pi * H := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  cases j
  · simp [twist_one, Complex.mul_re, Complex.mul_im]
    nlinarith [Real.pi_pos]
  · simp [twist_two, Complex.mul_re, Complex.mul_im]
    nlinarith [Real.pi_pos]
  · simp only [twist_three, zero_mul, Complex.zero_re]
    nlinarith [Real.pi_pos]

theorem uniform_log_norm_kernel_left_strip [PositiveArgument] {α₁ α₂ H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hH : 1 ≤ H) (j : Branch) (n : ℕ) :
    ∃ B ≥ 0, ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      Real.log ‖normalizedKernel α₁ α₂ j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        -T * Real.log T + (1 + |Real.log PositiveArgument.value|) * T + (α₁ * n + α₂ * n + 4) * Real.log T + B := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_Gamma_strip_shift
    (D := α₁ * n + α₂ * n + 2) (H := H) (by positivity) (by linarith)
  refine ⟨max 0 (5 * C + 3 * Real.log Real.pi + 3 * Real.log 4 +
    2 * Real.pi * H + |gammaNormError 2|), le_max_left _ _, ?_⟩
  filter_upwards [hb] with T hT y hy hyH
  have hx : -(T : ℂ) + (y : ℂ) * Complex.I ∈ kernelDomain α₁ α₂ n := by
    constructor
    · rw [Complex.mem_slitPlane_iff]
      right
      simpa using (show y ≠ 0 by intro h; norm_num [h] at hy)
    · change (-(T : ℂ) + (y : ℂ) * Complex.I).re < _
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
      exact lt_min (by nlinarith [mul_nonneg h₁.le (Nat.cast_nonneg (α := ℝ) n)])
        (by nlinarith [mul_nonneg h₂.le (Nat.cast_nonneg (α := ℝ) n)])
  have hsh : ∀ a : ℝ, 0 ≤ a → a ≤ α₁ * n + α₂ * n + 2 →
      |Real.log ‖Complex.Gamma ((T : ℂ) + (a : ℂ) - (y : ℂ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma (T : ℂ)‖ - a * Real.log (T - 1)| ≤ C := by
    intro a ha haD
    simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      hT.2 a ha haD (-y) (by simpa using hyH)
  have hzero : Real.log ‖Complex.Gamma (T : ℂ)‖ - C ≤
      Real.log ‖Complex.Gamma (-(-(T : ℂ) + (y : ℂ) * Complex.I))‖ := by
    have h := (abs_le.mp (hsh 0 le_rfl (by positivity))).1
    simp only [Complex.ofReal_zero, add_zero, zero_mul, sub_zero] at h
    rw [show -(-(T : ℂ) + (y : ℂ) * Complex.I) = (T : ℂ) - (y : ℂ) * Complex.I by ring]
    linarith
  have hright : ∀ a : ℝ, 0 ≤ a → a * n + 1 ≤ α₁ * n + α₂ * n + 2 →
      Real.log ‖Complex.Gamma ((a : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I) + 1)‖ ≤
        Real.log ‖Complex.Gamma (T : ℂ)‖ + (a * n + 1) * Real.log (T - 1) + C := by
    intro a ha haD
    have h := (abs_le.mp (hsh (a * n + 1) (by positivity) haD)).2
    rw [show (T : ℂ) + ((a * n + 1 : ℝ) : ℂ) - (y : ℂ) * Complex.I =
      (a : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I) + 1 by push_cast; ring] at h
    linarith
  have hlogx : 0 ≤ Real.log ‖-(T : ℂ) + (y : ℂ) * Complex.I‖ := by
    apply Real.log_nonneg
    have h := Complex.abs_re_le_norm (-(T : ℂ) + (y : ℂ) * Complex.I)
    simp [Complex.mul_re, abs_of_nonneg (show 0 ≤ T by linarith [hT.1])] at h
    linarith [hT.1]
  have hreflect := log_norm_Gamma_reflection
    (z := -(T : ℂ) + (y : ℂ) * Complex.I)
    (by simp [Complex.mul_re]; linarith [hT.1])
    (by simpa using (show y ≠ 0 by intro h; norm_num [h] at hy))
  have hlog : (α₁ * n + α₂ * n + 2) * Real.log (T - 1) ≤
      (α₁ * n + α₂ * n + 2) * Real.log T :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hT.1]) (by linarith))
      (by positivity)
  have htwist : (kernelTwist j * (-(T : ℂ) + (y : ℂ) * Complex.I)).re ≤
      2 * Real.pi * H + |Real.log PositiveArgument.value| * T := by
    have h := twist_re_le j (z := -(T : ℂ) + (y : ℂ) * Complex.I) (by simpa using hyH)
    simp only [kernelTwist, sub_mul, Complex.sub_re,
      Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero] at *
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self (Real.log PositiveArgument.value))
      (show 0 ≤ T by linarith [hT.1])]
  nlinarith [log_norm_kernel j n hx, log_norm_Gamma_real_lower hT.1, htwist,
    log_norm_sine_tail_lower (z := -(T : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy),
    twist_re_le j (z := -(T : ℂ) + (y : ℂ) * Complex.I) (by simpa using hyH),
    hright α₁ h₁.le (by nlinarith [mul_nonneg h₂.le (Nat.cast_nonneg (α := ℝ) n)]),
    hright α₂ h₂.le (by nlinarith [mul_nonneg h₁.le (Nat.cast_nonneg (α := ℝ) n)]),
    le_max_right 0 (5 * C + 3 * Real.log Real.pi + 3 * Real.log 4 +
      2 * Real.pi * H + |gammaNormError 2|)]

/-- For each fixed index, the actual normalizedKernel decays faster than every exponential
on the left, uniformly in a bounded strip separated from the real axis. -/
theorem uniform_kernel_left_decay [PositiveArgument] {α₁ α₂ H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hH : 1 ≤ H) (j : Branch) (n : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      ‖normalizedKernel α₁ α₂ j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (-q * T) := by
  obtain ⟨B, _, hb⟩ := uniform_log_norm_kernel_left_strip h₁ h₂ hH j n
  filter_upwards [hb, eventually_log_tail_le (α₁ * n + α₂ * n + 4) B (q + |Real.log PositiveArgument.value|),
    eventually_ge_atTop (0 : ℝ)]
    with T hT hq hT0 y hy hyH
  exact (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (by linarith [hT y hy hyH, hq.2]))

theorem eventually_shifted_pow_le_exp {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    ∀ᶠ T : ℝ in atTop, (T + D) ^ k ≤ Real.exp T := by
  have h := (Real.isLittleO_pow_exp_atTop (n := k)).const_mul_left ((1 + D) ^ k)
  filter_upwards [h.def zero_lt_one, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
  calc
    (T + D) ^ k ≤ ((1 + D) * T) ^ k := pow_le_pow_left₀ (by linarith)
      (by nlinarith [mul_le_mul_of_nonneg_left hT₁ hD]) k
    _ = (1 + D) ^ k * T ^ k := mul_pow _ _ _
    _ ≤ Real.exp T := by simpa only [Real.norm_of_nonneg (by positivity :
      0 ≤ (1 + D) ^ k * T ^ k), Real.norm_of_nonneg (Real.exp_pos T).le, one_mul] using hT

theorem norm_polynomial_left_le {T y H : ℝ} (hT : 0 ≤ T) (hy : |y| ≤ H) (n : ℕ) :
    ‖(n : ℂ) - (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ T + ((n : ℝ) + H) := by
  calc
    _ ≤ ‖(n : ℂ)‖ + ‖-(T : ℂ) + (y : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ ≤ ‖(n : ℂ)‖ + (‖-(T : ℂ)‖ + ‖(y : ℂ) * Complex.I‖) :=
      add_le_add (le_refl _) (norm_add_le _ _)
    _ = (n : ℝ) + (T + |y|) := by simp [abs_of_nonneg hT]
    _ ≤ T + ((n : ℝ) + H) := by linarith

theorem uniform_weighted_kernel_left_decay [PositiveArgument] {α₁ α₂ H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hH : 1 ≤ H) (j : Branch) (n k : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      ‖((n : ℂ) - (-(T : ℂ) + (y : ℂ) * Complex.I)) ^ k *
        normalizedKernel α₁ α₂ j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (-q * T) := by
  filter_upwards [uniform_kernel_left_decay h₁ h₂ hH j n (q + 1),
    eventually_shifted_pow_le_exp (D := (n : ℝ) + H) (by positivity) k,
    eventually_ge_atTop (0 : ℝ)] with T hK hP hT y hy hyH
  calc
    _ = ‖(n : ℂ) - (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ^ k *
        ‖normalizedKernel α₁ α₂ j n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ := by rw [norm_mul, norm_pow]
    _ ≤ Real.exp T * Real.exp (-(q + 1) * T) :=
      mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) (norm_polynomial_left_le hT hyH n) k).trans hP)
        (hK y hy hyH) (norm_nonneg _) (Real.exp_pos T).le
    _ = Real.exp (-q * T) := by rw [← Real.exp_add]; congr 1; ring

end ThisWork.Analytic
