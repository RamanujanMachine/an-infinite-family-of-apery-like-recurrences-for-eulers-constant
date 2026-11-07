module

public import ThisWork.Argument
public import ThisWork.ReflectedGammaNorm
public import ThisWork.Parameters

/-! Gamma-norm error estimates uniform under the saddle scaling. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem norm_real_scale_le {R M : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖(R : ℂ) * s‖ ≤ R * M := by
  rw [norm_mul, Complex.norm_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left hs hR

theorem uniform_scaled_gammaNormError_right {κ M : ℝ} (hκ : 0 < κ) (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re →
      |gammaNormError ((R : ℂ) * s)| ≤ C * (1 + Real.log R) := by
  let B := |gammaNormError 2| + 2 * |Real.log M| + 2 * M / κ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B + 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 / κ)] with R hR₁ hRκ
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR₁
  refine ⟨hR, fun s hs hκs => ?_⟩
  have hden : R * κ ≤ ((R : ℂ) * s).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left hκs hR.le
  have h2 : 2 ≤ ((R : ℂ) * s).re := ((div_le_iff₀ hκ).mp hRκ).trans hden
  have hnorm := norm_real_scale_le hR.le hs
  have hlog : Real.log (((R : ℂ) * s).re) ≤ Real.log R + Real.log M := by
    have h := Real.log_le_log (show 0 < ((R : ℂ) * s).re by linarith)
      ((Complex.re_le_norm _).trans hnorm)
    simpa only [Real.log_mul hR.ne' hM.ne'] using h
  have him : |((R : ℂ) * s).im| ≤ R * M := (Complex.abs_im_le_norm _).trans hnorm
  have hratio : 2 * |((R : ℂ) * s).im| / ((R : ℂ) * s).re ≤ 2 * M / κ := by
    apply (div_le_div_iff₀ (by linarith : 0 < ((R : ℂ) * s).re) hκ).mpr
    nlinarith [mul_le_mul_of_nonneg_right him hκ.le, mul_le_mul_of_nonneg_left hden hM.le]
  have herror : |gammaNormError ((R : ℂ) * s)| ≤ B + 2 * Real.log R := by
    dsimp only [B]
    linarith [abs_gammaNormError_right h2, le_abs_self (Real.log M)]
  exact herror.trans (by nlinarith [Real.log_nonneg hR₁])

theorem uniform_scaled_gammaNormError_left {κ η M : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, ‖s‖ ≤ M → s.re ≤ -κ → η ≤ |s.im| →
      |gammaNormError ((R : ℂ) * s)| ≤ C * (1 + Real.log R) := by
  let B := |gammaNormError 2| + |Real.log Real.pi| + Real.log 4 + 3 * |Real.log M| + 2 * M / κ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have ha : 0 < 2 * Real.pi * η := by positivity
  refine ⟨B + 3, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 / κ), eventually_exp_decay_bounds ha]
    with R hR₁ hRκ hdec
  have hR := hdec.1
  refine ⟨hR, fun s hs hκs hηs => ?_⟩
  have hden : R * κ ≤ -((R : ℂ) * s).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left hκs hR.le]
  have h2 : ((R : ℂ) * s).re ≤ -2 := by
    have h := (div_le_iff₀ hκ).mp hRκ
    linarith
  have hnorm := norm_real_scale_le hR.le hs
  have hnorm0 : 0 < ‖(R : ℂ) * s‖ := by
    have h := Complex.abs_re_le_norm ((R : ℂ) * s)
    rw [abs_of_neg (show ((R : ℂ) * s).re < 0 by linarith)] at h
    linarith
  have hlog : Real.log ‖(R : ℂ) * s‖ ≤ Real.log R + Real.log M := by
    simpa only [Real.log_mul hR.ne' hM.ne'] using Real.log_le_log hnorm0 hnorm
  have himEq : |((R : ℂ) * s).im| = R * |s.im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos hR]
  have hexp : Real.exp (-2 * Real.pi * |((R : ℂ) * s).im|) ≤ Real.exp (-(2 * Real.pi * η) * R) := by
    apply Real.exp_le_exp.mpr
    rw [himEq]
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηs hR.le)
      (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).le]
  have him : |((R : ℂ) * s).im| ≤ R * M := (Complex.abs_im_le_norm _).trans hnorm
  have hratio : 2 * |((R : ℂ) * s).im| / (-((R : ℂ) * s).re) ≤ 2 * M / κ := by
    apply (div_le_div_iff₀ (by linarith : 0 < -((R : ℂ) * s).re) hκ).mpr
    nlinarith [mul_le_mul_of_nonneg_right him hκ.le, mul_le_mul_of_nonneg_left hden hM.le]
  have herror : |gammaNormError ((R : ℂ) * s)| ≤ B + 3 * Real.log R := by
    dsimp only [B]
    linarith [abs_gammaNormError_left h2 (hexp.trans hdec.2.1), le_abs_self (Real.log M)]
  exact herror.trans (by nlinarith [Real.log_nonneg hR₁])

theorem gammaNormError_rate_of_scaled_bound {K : Set ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ R : ℝ in atTop, ∀ s ∈ K, |gammaNormError ((R : ℂ) * s)| ≤ C * (1 + Real.log R)) :
    ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      |gammaNormError ((largeScale n : ℂ) * s)| ≤ D * (n : ℝ) ^ (1 / 3 : ℝ) := by
  refine ⟨3 * C, by positivity, ?_⟩
  filter_upwards [largeScale_tendsto.eventually hb, eventually_ge_atTop (1 : ℕ)] with n hn hn₁ s hs
  exact (hn s hs).trans ((mul_le_mul_of_nonneg_left (one_add_log_largeScale_le hn₁) hC).trans_eq (by ring))

/-- Uniform Gamma error on the actual fixed saddle disks, at the precision
needed for the exponential norm estimate in Lemma 8. -/
theorem uniform_gammaNormError_disk [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      |gammaNormError ((largeScale n : ℂ) * s)| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  let c := saddleScale α₁ α₂
  have hc : 0 < c := saddleScale_pos h₁ h₂
  cases j
  · obtain ⟨C, hC, hb⟩ := uniform_scaled_gammaNormError_left (κ := c / 4) (η := c / 4) (M := 5 * c / 4)
      (by positivity) (by positivity) (by positivity)
    exact gammaNormError_rate_of_scaled_bound hC (hb.mono (fun R hR s hs =>
      hR.2 s (saddleDisk_norm_le hc .one hs)
        (saddleDisk_region hc .one hs).1 (saddleDisk_region hc .one hs).2))
  · obtain ⟨C, hC, hb⟩ := uniform_scaled_gammaNormError_left (κ := c / 4) (η := c / 4) (M := 5 * c / 4)
      (by positivity) (by positivity) (by positivity)
    exact gammaNormError_rate_of_scaled_bound hC (hb.mono (fun R hR s hs =>
      hR.2 s (saddleDisk_norm_le hc .two hs)
        (saddleDisk_region hc .two hs).1 (saddleDisk_region hc .two hs).2))
  · obtain ⟨C, hC, hb⟩ := uniform_scaled_gammaNormError_right (κ := c / 2) (M := 5 * c / 4)
      (by positivity) (by positivity)
    exact gammaNormError_rate_of_scaled_bound hC (hb.mono (fun R hR s hs =>
      hR.2 s (saddleDisk_norm_le hc .three hs) (saddleDisk_region hc .three hs)))

end ThisWork.Analytic
