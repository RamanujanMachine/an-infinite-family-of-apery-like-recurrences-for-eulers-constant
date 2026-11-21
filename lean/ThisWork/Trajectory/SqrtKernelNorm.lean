module
public import ThisWork.Trajectory.SqrtAffineGammaNorm
public import ThisWork.Trajectory.CanonicalMoments
public import ThisWork.KernelNorm
/-! The absolute Gamma normalization of the canonical square-root kernel. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

theorem doubleScale_pos {m d n : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (hn : 0 < n) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    0 < doubleScale m d A₁ A₂ z n := by
  apply mul_pos
  · apply Real.Gamma_pos_of_pos
    exact mul_pos (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr hn)
  · exact mul_pos (gammaScale_pos h₁ h₂ n) (pow_pos hz _)

theorem scaled_sqrt_stirlingMain {d n : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hn : 0 < n) {s : ℂ} (hs : s ≠ 0) :
    2 * stirlingMain ((sqrtScale n : ℂ) * s) +
      (sqrtScale n : ℂ) * s * (Real.log ((d : ℝ) * n) : ℂ) -
      (sqrtScale n : ℂ) * s * (Real.log (A₁ * n) : ℂ) -
      (sqrtScale n : ℂ) * s * (Real.log (A₂ * n) : ℂ) -
      (Real.log z : ℂ) * ((sqrtScale n : ℂ) * s) =
        (sqrtScale n : ℂ) * sqrtPhase (doubleSaddleScale d A₁ A₂ z) s := by
  have hR := sqrtScale_pos hn
  have he := limitingSqrtEquation_eq_logs hd h₁ h₂ hz .three hs
  simp only [limitingSqrtEquation, twist_three, add_zero] at he
  have hr : (2 : ℂ) * (Real.log (sqrtScale n) : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    by exact_mod_cast log_sqrtScale hn
  rw [stirlingMain, Complex.log_ofReal_mul hR hs,
    Real.log_mul (Nat.cast_pos.mpr hd).ne' (Nat.cast_pos.mpr hn).ne',
    Real.log_mul h₁.ne' (Nat.cast_pos.mpr hn).ne',
    Real.log_mul h₂.ne' (Nat.cast_pos.mpr hn).ne']
  have hp : sqrtPhase (doubleSaddleScale d A₁ A₂ z) s =
      s * (sqrtEquation (doubleSaddleScale d A₁ A₂ z) s - 2) := by
    simp only [sqrtPhase, limitingPhase, limitingEquation, twist_three, add_zero, sqrtEquation]
    ring
  rw [hp, he]
  simp only [Complex.ofReal_add]
  linear_combination (sqrtScale n : ℂ) * s * hr

theorem log_norm_canonical_kernel {m d n : ℕ} {A₁ A₂ z : ℝ} (hz : 0 < z)
    {x : ℂ} (hx : x ∈ kernelDomain A₁ A₂ n) :
    Real.log ‖kernel m d A₁ A₂ z .three n x‖ =
      2 * Real.log ‖Complex.Gamma x‖ +
      Real.log ‖Complex.Gamma ((d : ℂ) * n + x)‖ +
      Real.log ‖Complex.Gamma ((A₁ : ℂ) * n - x + 1)‖ +
      Real.log ‖Complex.Gamma ((A₂ : ℂ) * n - x + 1)‖ +
      Real.log z * ((m : ℝ) * n - x.re) := by
  let : PositiveArgument := ⟨z, hz⟩
  have h₀ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (not_neg_nat_of_mem_slitPlane hx.1))
  have hD := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero
    (not_neg_nat_of_mem_slitPlane (add_nat_mul_mem_slitPlane d n hx.1)))
  rw [kernel_eq_gamma_quotient hz m d A₁ A₂ .three n (not_neg_nat_of_mem_slitPlane hx.1),
    norm_mul, Complex.norm_exp, norm_mul, norm_div,
    Real.log_mul (Real.exp_ne_zero _) (mul_ne_zero (div_ne_zero hD h₀)
      (norm_ne_zero_iff.mpr (Analytic.kernel_ne_zero .three n hx))), Real.log_exp,
    Real.log_mul (div_ne_zero hD h₀) (norm_ne_zero_iff.mpr (Analytic.kernel_ne_zero .three n hx)),
    Real.log_div hD h₀, Analytic.log_norm_kernel .three n hx]
  simp only [Analytic.kernelTwist, twist_three, zero_sub, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero]
  have hv : PositiveArgument.value = z := rfl
  rw [hv]
  ring

theorem log_doubleScale {m d n : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (hn : 0 < n) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    Real.log (doubleScale m d A₁ A₂ z n) =
      Real.log ‖Complex.Gamma (((d : ℝ) * n : ℝ) : ℂ)‖ +
      Real.log ‖Complex.Gamma ((A₁ * n + 1 : ℝ) : ℂ)‖ +
      Real.log ‖Complex.Gamma ((A₂ * n + 1 : ℝ) : ℂ)‖ + ((m : ℝ) * n) * Real.log z := by
  have hD : 0 < Real.Gamma ((d : ℝ) * n) := Real.Gamma_pos_of_pos (by positivity)
  rw [doubleScale, equalScale, Real.log_mul hD.ne' (mul_pos (gammaScale_pos h₁ h₂ n) (pow_pos hz _)).ne',
    Real.log_mul (gammaScale_pos h₁ h₂ n).ne' (pow_pos hz _).ne', log_gammaScale h₁ h₂,
    Real.log_pow]
  simp only [Complex.Gamma_ofReal]
  rw [Complex.norm_of_nonneg hD.le]
  push_cast
  ring

theorem uniform_log_norm_canonical_kernel_disk {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      |Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖ -
        Real.log (doubleScale m d A₁ A₂ z n) -
        sqrtScale n * (sqrtPhase (doubleSaddleScale d A₁ A₂ z) s).re| ≤
          C * (1 + Real.log (sqrtScale n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  have hM : 0 < 5 * c / 4 := by positivity
  obtain ⟨C₀, hC₀, hb₀⟩ := uniform_scaled_gammaNormError_right (κ := c / 2) (by positivity) hM
  obtain ⟨C₁, hC₁, hb₁⟩ := uniform_log_norm_Gamma_sqrt_affine h₁ hM
  obtain ⟨C₂, hC₂, hb₂⟩ := uniform_log_norm_Gamma_sqrt_affine h₂ hM
  obtain ⟨CD, hCD, hbD⟩ := uniform_log_norm_Gamma_sqrt_affine (Nat.cast_pos.mpr hd) hM
  refine ⟨2 * C₀ + C₁ + C₂ + CD, by positivity, ?_⟩
  filter_upwards [sqrtScale_tendsto.eventually hb₀, hb₁, hb₂, hbD,
    eventually_sqrtDisk_mapsTo_kernelDomain h₁ h₂ hc,
    sqrtScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn₀ hn₁ hn₂ hnD hdom hR₁ s hs
  have hsM : ‖s‖ ≤ 5 * c / 4 := saddleDisk_norm_le hc .three hs
  have he₀ := hn₀.2 s hsM (saddleDisk_region hc .three hs)
  have he₁ := (hn₁ s hsM).1
  have he₂ := (hn₂ s hsM).1
  have heD := (hnD s hsM).2
  have hk := log_norm_canonical_kernel (m := m) (d := d) hz (hdom.2 hs)
  have hH := log_doubleScale (m := m) hd hdom.1 h₁ h₂ hz
  have hm := congrArg Complex.re (scaled_sqrt_stirlingMain hd h₁ h₂ hz hdom.1
    (Complex.slitPlane_ne_zero (saddleDisk_mem_slitPlane hc .three hs)))
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at hm hk
  norm_num at hm
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at he₁ he₂ heD hH
  have heq : Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖ -
      Real.log (doubleScale m d A₁ A₂ z n) - sqrtScale n * (sqrtPhase c s).re =
      2 * gammaNormError ((sqrtScale n : ℂ) * s) +
      (Real.log ‖Complex.Gamma ((A₁ : ℂ) * n - (sqrtScale n : ℂ) * s + 1)‖ -
        Real.log ‖Complex.Gamma (((A₁ * n + 1 : ℝ)) : ℂ)‖ + sqrtScale n * s.re * Real.log (A₁ * n)) +
      (Real.log ‖Complex.Gamma ((A₂ : ℂ) * n - (sqrtScale n : ℂ) * s + 1)‖ -
        Real.log ‖Complex.Gamma (((A₂ * n + 1 : ℝ)) : ℂ)‖ + sqrtScale n * s.re * Real.log (A₂ * n)) +
      (Real.log ‖Complex.Gamma ((d : ℂ) * n + (sqrtScale n : ℂ) * s)‖ -
        Real.log ‖Complex.Gamma (((d : ℝ) * n : ℝ) : ℂ)‖ - sqrtScale n * s.re * Real.log ((d : ℝ) * n)) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
    dsimp only [gammaNormError, c]
    linear_combination hk - hH + hm
  rw [heq]
  have hlog : 0 ≤ Real.log (sqrtScale n) := Real.log_nonneg hR₁
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at heq ⊢
  rw [abs_le] at he₀ he₁ he₂ heD ⊢
  dsimp only [gammaNormError] at he₀ ⊢
  constructor <;> nlinarith

theorem uniform_log_norm_canonical_kernel_near_saddle {d : ℕ} {A₁ A₂ z D : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hD : 0 ≤ D) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖s - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      |Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖ -
        Real.log (doubleScale m d A₁ A₂ z n) + 2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n| ≤
          C * (1 + Real.log (sqrtScale n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_canonical_kernel_disk hd h₁ h₂ hz m
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
