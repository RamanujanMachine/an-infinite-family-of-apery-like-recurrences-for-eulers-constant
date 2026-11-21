module
public import ThisWork.Trajectory.ReflectedLocalMoments
public import ThisWork.Trajectory.SqrtKernelNorm
/-! Gamma normalization of the reflected growing saddle. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

theorem log_norm_reflectedScaledKernel (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (s : ℂ)
    (hD : 0 < ((d : ℂ) * n - (sqrtScale n : ℂ) * s).re)
    (h₁ : 0 < ((A₁ : ℂ) * n + (sqrtScale n : ℂ) * s + 1).re)
    (h₂ : 0 < ((A₂ : ℂ) * n + (sqrtScale n : ℂ) * s + 1).re)
    (hs : 0 < ((sqrtScale n : ℂ) * s).re) :
    Real.log ‖reflectedScaledKernel m d A₁ A₂ z n s‖ =
      Real.log ‖Complex.Gamma ((d : ℂ) * n - (sqrtScale n : ℂ) * s)‖ +
      Real.log ‖Complex.Gamma ((A₁ : ℂ) * n + (sqrtScale n : ℂ) * s + 1)‖ +
      Real.log ‖Complex.Gamma ((A₂ : ℂ) * n + (sqrtScale n : ℂ) * s + 1)‖ -
      2 * Real.log ‖Complex.Gamma ((sqrtScale n : ℂ) * s)‖ -
      2 * Real.log ‖(sqrtScale n : ℂ) * s‖ + Real.log z * ((m : ℝ) * n + sqrtScale n * s.re) := by
  have nD := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hD)
  have n₁ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos h₁)
  have n₂ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos h₂)
  have ns := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hs)
  have nx : (sqrtScale n : ℂ) * s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have nnx := norm_ne_zero_iff.mpr nx
  have hg : Complex.Gamma (1 + (sqrtScale n : ℂ) * s) =
      ((sqrtScale n : ℂ) * s) * Complex.Gamma ((sqrtScale n : ℂ) * s) := by
    rw [add_comm, Complex.Gamma_add_one _ nx]
  simp only [reflectedScaledKernel, reflectedKernel, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [hg]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_exp]
  rw [norm_mul] at nnx
  rw [Real.log_mul (div_ne_zero (mul_ne_zero (mul_ne_zero nD n₁) n₂) (pow_ne_zero 2 (mul_ne_zero nnx ns)))
      (Real.exp_ne_zero _),
    Real.log_div (mul_ne_zero (mul_ne_zero nD n₁) n₂) (pow_ne_zero 2 (mul_ne_zero nnx ns)),
    Real.log_mul (mul_ne_zero nD n₁) n₂, Real.log_mul nD n₁,
    Real.log_pow, Real.log_mul nnx ns, Real.log_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero, sub_zero]
  norm_num
  ring

theorem uniform_log_norm_reflected_kernel_disk {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      |Real.log ‖reflectedScaledKernel m d A₁ A₂ z n s‖ - Real.log (doubleScale m d A₁ A₂ z n) +
        sqrtScale n * (sqrtPhase (doubleSaddleScale d A₁ A₂ z) s).re| ≤ C * (1 + Real.log (sqrtScale n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  let M := 5 * c / 4
  let L := |Real.log (c / 2)| + |Real.log M|
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  have hM : 0 < M := by dsimp only [M]; positivity
  have hL : 0 ≤ L := add_nonneg (abs_nonneg _) (abs_nonneg _)
  obtain ⟨C₀, hC₀, hb₀⟩ := uniform_scaled_gammaNormError_right (κ := c / 2) (by positivity) hM
  obtain ⟨C₁, hC₁, hb₁⟩ := uniform_log_norm_Gamma_sqrt_affine h₁ hM
  obtain ⟨C₂, hC₂, hb₂⟩ := uniform_log_norm_Gamma_sqrt_affine h₂ hM
  obtain ⟨CD, hCD, hbD⟩ := uniform_log_norm_Gamma_sqrt_affine (Nat.cast_pos.mpr hd) hM
  refine ⟨2 * C₀ + C₁ + C₂ + CD + 2 + 2 * L, by positivity, ?_⟩
  filter_upwards [sqrtScale_tendsto.eventually hb₀, hb₁, hb₂, hbD,
    eventually_right_factor_conditions (Nat.cast_pos.mpr hd) M,
    sqrtScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)), eventually_gt_atTop (0 : ℕ)]
    with n hn₀ hn₁ hn₂ hnD hD hR₁ hn s hs
  have hR := sqrtScale_pos hn
  have hsM : ‖s‖ ≤ M := saddleDisk_norm_le hc .three hs
  have hre : c / 2 ≤ s.re := saddleDisk_region hc .three hs
  have hspos : 0 < s.re := by linarith
  have hs0 := Complex.slitPlane_ne_zero (saddleDisk_mem_slitPlane hc .three hs)
  have he₀ := hn₀.2 s hsM hre
  have he₁ := (hn₁ (-s) (by simpa only [norm_neg] using hsM)).1
  have he₂ := (hn₂ (-s) (by simpa only [norm_neg] using hsM)).1
  have heD := (hnD (-s) (by simpa only [norm_neg] using hsM)).2
  have hsr : ((sqrtScale n : ℂ) * s).re = sqrtScale n * s.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hdR : 0 < ((d : ℂ) * n - (sqrtScale n : ℂ) * s).re := by
    have hb := mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans hsM) hR.le
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith [hD.1, hD.2]
  have hAR (A : ℝ) (hA : 0 < A) : 0 < ((A : ℂ) * n + (sqrtScale n : ℂ) * s + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.one_re, zero_mul, mul_zero, sub_zero]
    positivity
  have hk := log_norm_reflectedScaledKernel m d A₁ A₂ z n s hdR (hAR A₁ h₁) (hAR A₂ h₂)
    (by rw [hsr]; positivity)
  have hH := log_doubleScale (m := m) hd hn h₁ h₂ hz
  have hm := congrArg Complex.re (scaled_sqrt_stirlingMain hd h₁ h₂ hz hn hs0)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at hm
  norm_num at hm
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.neg_re, mul_neg, sub_neg_eq_add,
    ← sub_eq_add_neg] at he₁ he₂ heD hH
  have heq : Real.log ‖reflectedScaledKernel m d A₁ A₂ z n s‖ - Real.log (doubleScale m d A₁ A₂ z n) +
      sqrtScale n * (sqrtPhase c s).re + 2 * Real.log ‖(sqrtScale n : ℂ) * s‖ =
      -2 * gammaNormError ((sqrtScale n : ℂ) * s) +
      (Real.log ‖Complex.Gamma ((A₁ : ℂ) * n + (sqrtScale n : ℂ) * s + 1)‖ -
        Real.log ‖Complex.Gamma ((A₁ * n + 1 : ℝ) : ℂ)‖ - sqrtScale n * s.re * Real.log (A₁ * n)) +
      (Real.log ‖Complex.Gamma ((A₂ : ℂ) * n + (sqrtScale n : ℂ) * s + 1)‖ -
        Real.log ‖Complex.Gamma ((A₂ * n + 1 : ℝ) : ℂ)‖ - sqrtScale n * s.re * Real.log (A₂ * n)) +
      (Real.log ‖Complex.Gamma ((d : ℂ) * n - (sqrtScale n : ℂ) * s)‖ -
        Real.log ‖Complex.Gamma (((d : ℝ) * n : ℝ) : ℂ)‖ + sqrtScale n * s.re * Real.log ((d : ℝ) * n)) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
    dsimp only [gammaNormError, c]
    linear_combination hk - hH - hm
  have hnorm : |Real.log ‖(sqrtScale n : ℂ) * s‖| ≤ Real.log (sqrtScale n) + L := by
    have hlo := Real.log_le_log (show 0 < c / 2 by positivity) (hre.trans (Complex.re_le_norm s))
    have hhi := Real.log_le_log (norm_pos_iff.mpr hs0) hsM
    rw [norm_mul, Complex.norm_of_nonneg hR.le, Real.log_mul hR.ne' (norm_ne_zero_iff.mpr hs0)]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (Real.log_nonneg hR₁)]
    dsimp only [L]
    apply add_le_add_right
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log (c / 2)), le_abs_self (Real.log M),
      neg_abs_le (Real.log (c / 2)), neg_abs_le (Real.log M), abs_nonneg (Real.log (c / 2)), abs_nonneg (Real.log M)]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at heq ⊢
  rw [abs_le] at he₀ he₁ he₂ heD hnorm ⊢
  dsimp only [gammaNormError] at he₀ heq
  have hlog := Real.log_nonneg hR₁
  constructor <;> nlinarith

theorem uniform_log_norm_reflected_kernel_near_saddle {d : ℕ} {A₁ A₂ z D : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hD : 0 ≤ D) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖s - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      |Real.log ‖reflectedScaledKernel m d A₁ A₂ z n s‖ -
        Real.log (doubleScale m d A₁ A₂ z n) - 2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n| ≤
          C * (1 + Real.log (sqrtScale n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_reflected_kernel_disk hd h₁ h₂ hz m
  obtain ⟨B, hB, hφ⟩ := limitingPhase_saddle_lipschitz hc .three
  refine ⟨C + (2 / 3 : ℝ) * B * D, by positivity, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ),
    sqrtScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hn₀ hR₁ s hs hdisp
  have hphase : |(sqrtPhase c s).re + 2 * c| ≤ (2 / 3 : ℝ) * B * (D / sqrtScale n) := by
    have h := hφ s hs
    simp only [rho_three, mul_one] at h
    have hps : limitingPhase .three c (c : ℂ) = -3 * (c : ℂ) := by
      simpa only [rho_three, mul_one] using limitingPhase_saddle .three hc
    have he : (sqrtPhase c s).re + 2 * c =
        (2 / 3 : ℝ) * (limitingPhase .three c s - limitingPhase .three c (c : ℂ)).re := by
      simp [sqrtPhase, hps, Complex.mul_re]
      ring
    rw [he, abs_mul]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans
      (mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hdisp hB)) (by norm_num : (0 : ℝ) ≤ 2 / 3))
  have hscaled : |sqrtScale n * ((sqrtPhase c s).re + 2 * c)| ≤ (2 / 3 : ℝ) * B * D := by
    rw [abs_mul, abs_of_pos (sqrtScale_pos hn₀)]
    exact (mul_le_mul_of_nonneg_left hphase (sqrtScale_pos hn₀).le).trans_eq (by
      field_simp)
  have hlog := Real.log_nonneg hR₁
  rw [abs_le] at hscaled ⊢
  have h := abs_le.mp (hn s hs)
  constructor <;> nlinarith

end ThisWork.Trajectory
