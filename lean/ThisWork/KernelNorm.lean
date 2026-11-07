module

public import ThisWork.Argument
public import ThisWork.ScaledGammaNorm
public import ThisWork.AffineGammaNorm

/-! Logarithmic norm of the actual Gamma-product normalizedKernel near its saddles. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem log_norm_kernel [PositiveArgument] {α₁ α₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ kernelDomain α₁ α₂ n) :
    Real.log ‖normalizedKernel α₁ α₂ j n x‖ = 3 * Real.log ‖Complex.Gamma x‖ +
      Real.log ‖Complex.Gamma ((α₁ : ℂ) * n - x + 1)‖ +
      Real.log ‖Complex.Gamma ((α₂ : ℂ) * n - x + 1)‖ + (kernelTwist j * x).re := by
  have hr := kernelDomain_right_re_pos hx
  have h₀ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (not_neg_nat_of_mem_slitPlane hx.1))
  have h₁ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hr.1)
  have h₂ := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hr.2)
  simp only [normalizedKernel, norm_mul, norm_pow, Complex.norm_exp]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h₀) h₁) h₂) (Real.exp_ne_zero _),
    Real.log_mul (mul_ne_zero (pow_ne_zero 3 h₀) h₁) h₂,
    Real.log_mul (pow_ne_zero 3 h₀) h₁, Real.log_pow, Real.log_exp]
  norm_num

theorem scaled_stirlingMain_kernel [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 0) :
    3 * stirlingMain ((largeScale n : ℂ) * s) -
      (largeScale n : ℂ) * s * (Real.log (α₁ * n) : ℂ) -
      (largeScale n : ℂ) * s * (Real.log (α₂ * n) : ℂ) +
      kernelTwist j * ((largeScale n : ℂ) * s) =
      (largeScale n : ℂ) * limitingPhase j (saddleScale α₁ α₂) s := by
  have hR := largeScale_pos hn
  have hscale : (3 : ℂ) * (Real.log (largeScale n) : ℂ) = 2 * (Real.log (n : ℝ) : ℂ) := by
    exact_mod_cast log_largeScale hn
  rw [stirlingMain, Complex.log_ofReal_mul hR hs, limitingPhase, limitingEquation_eq_logs h₁ h₂ j hs,
    Real.log_mul h₁.ne' (Nat.cast_ne_zero.mpr hn.ne'), Real.log_mul h₂.ne' (Nat.cast_ne_zero.mpr hn.ne')]
  simp only [Complex.ofReal_add]
  linear_combination (largeScale n : ℂ) * s * hscale

theorem scaled_stirlingMain_kernel_re [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 0) :
    3 * (stirlingMain ((largeScale n : ℂ) * s)).re -
      largeScale n * s.re * Real.log (α₁ * n) - largeScale n * s.re * Real.log (α₂ * n) +
      (kernelTwist j * ((largeScale n : ℂ) * s)).re =
      largeScale n * (limitingPhase j (saddleScale α₁ α₂) s).re := by
  simpa [Complex.mul_re] using congrArg Complex.re (scaled_stirlingMain_kernel h₁ h₂ j hn hs)

theorem log_gammaScale {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (n : ℕ) :
    Real.log (gammaScale α₁ α₂ n) =
      Real.log ‖Complex.Gamma ((α₁ * n + 1 : ℝ) : ℂ)‖ +
      Real.log ‖Complex.Gamma ((α₂ * n + 1 : ℝ) : ℂ)‖ := by
  have hΓ₁ : 0 < Real.Gamma (α₁ * n + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hΓ₂ : 0 < Real.Gamma (α₂ * n + 1) := Real.Gamma_pos_of_pos (by positivity)
  rw [gammaScale, Real.log_mul hΓ₁.ne' hΓ₂.ne', Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.norm_of_nonneg hΓ₁.le, Complex.norm_of_nonneg hΓ₂.le]

@[expose] noncomputable def rightGammaNormError (α : ℝ) (n : ℕ) (s : ℂ) : ℝ :=
  Real.log ‖Complex.Gamma ((α : ℂ) * n - (largeScale n : ℂ) * s + 1)‖ -
    Real.log ‖Complex.Gamma ((α * n + 1 : ℝ) : ℂ)‖ + largeScale n * s.re * Real.log (α * n)

theorem log_norm_kernel_error [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 0)
    (hx : (largeScale n : ℂ) * s ∈ kernelDomain α₁ α₂ n) :
    Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ - Real.log (gammaScale α₁ α₂ n) -
      largeScale n * (limitingPhase j (saddleScale α₁ α₂) s).re =
      3 * gammaNormError ((largeScale n : ℂ) * s) +
        rightGammaNormError α₁ n s + rightGammaNormError α₂ n s := by
  have hk := log_norm_kernel j n hx
  have hH := log_gammaScale h₁ h₂ n
  have hm := scaled_stirlingMain_kernel_re h₁ h₂ j hn hs
  dsimp only [gammaNormError, rightGammaNormError]
  linarith

/-- The normalized logarithmic normalizedKernel has the limiting phase with the
`O(n^(1/3))` error asserted in Appendix A, uniformly on all three saddle disks. -/
theorem uniform_log_norm_kernel_disk [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      |Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ - Real.log (gammaScale α₁ α₂ n) -
        largeScale n * (limitingPhase j (saddleScale α₁ α₂) s).re| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨C₀, hC₀, hb₀⟩ := uniform_gammaNormError_disk h₁ h₂ j
  have hM : 0 < 5 * saddleScale α₁ α₂ / 4 := by have hc := saddleScale_pos h₁ h₂; positivity
  obtain ⟨C₁, hC₁, hb₁⟩ := uniform_log_norm_Gamma_affine h₁ hM
  obtain ⟨C₂, hC₂, hb₂⟩ := uniform_log_norm_Gamma_affine h₂ hM
  refine ⟨3 * C₀ + C₁ + C₂, by positivity, ?_⟩
  filter_upwards [hb₀, hb₁, hb₂, eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j]
    with n hn₀ hn₁ hn₂ hdom s hs
  rw [log_norm_kernel_error h₁ h₂ j hdom.1
    (Complex.slitPlane_ne_zero (saddleDisk_mem_slitPlane (saddleScale_pos h₁ h₂) j hs)) (hdom.2 hs)]
  have he₁ : |rightGammaNormError α₁ n s| ≤ C₁ * (n : ℝ) ^ (1 / 3 : ℝ) :=
    hn₁ s (saddleDisk_norm_le (saddleScale_pos h₁ h₂) j hs)
  have he₂ : |rightGammaNormError α₂ n s| ≤ C₂ * (n : ℝ) ^ (1 / 3 : ℝ) :=
    hn₂ s (saddleDisk_norm_le (saddleScale_pos h₁ h₂) j hs)
  calc
    _ ≤ |3 * gammaNormError ((largeScale n : ℂ) * s)| + |rightGammaNormError α₁ n s| +
        |rightGammaNormError α₂ n s| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = 3 * |gammaNormError ((largeScale n : ℂ) * s)| + |rightGammaNormError α₁ n s| +
        |rightGammaNormError α₂ n s| := by rw [abs_mul]; norm_num
    _ ≤ (3 * C₀ + C₁ + C₂) * (n : ℝ) ^ (1 / 3 : ℝ) := by nlinarith [hn₀ s hs]

theorem limitingPhase_saddle_lipschitz {c : ℝ} (hc : 0 < c) (j : Branch) :
    ∃ B ≥ 0, ∀ s ∈ saddleDisk c j,
      ‖limitingPhase j c s - limitingPhase j c ((c : ℂ) * rho j)‖ ≤ B * ‖s - (c : ℂ) * rho j‖ := by
  have hcont : ContinuousOn (limitingEquation j c) (saddleDisk c j) :=
    fun s hs => (hasDerivAt_limitingEquation j hc ((div_pos_real_mem_slitPlane_iff hc s).mpr
      (saddleDisk_mem_slitPlane hc j hs))).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall ((c : ℂ) * rho j) (c / 4)).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  exact (convex_closedBall ((c : ℂ) * rho j) (c / 4)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_limitingPhase j hc ((div_pos_real_mem_slitPlane_iff hc u).mpr
      (saddleDisk_mem_slitPlane hc j hu))).hasDerivWithinAt)
    (fun u hu => (hB u hu).trans (le_max_left _ _)) (mem_closedBall_self (by positivity)) hs

theorem uniform_log_norm_kernel_near_saddle [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖s - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      |Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ - Real.log (gammaScale α₁ α₂ n) +
        3 * saddleScale α₁ α₂ * (rho j).re * largeScale n| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hk⟩ := uniform_log_norm_kernel_disk h₁ h₂ j
  obtain ⟨B, hB, hφ⟩ := limitingPhase_saddle_lipschitz (saddleScale_pos h₁ h₂) j
  refine ⟨C + B * D, by positivity, ?_⟩
  filter_upwards [hk, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ s hs hdisp
  have hphase := (Complex.abs_re_le_norm
    (limitingPhase j (saddleScale α₁ α₂) s -
      limitingPhase j (saddleScale α₁ α₂) ((saddleScale α₁ α₂ : ℂ) * rho j))).trans
    ((hφ s hs).trans (mul_le_mul_of_nonneg_left hdisp hB))
  rw [Complex.sub_re] at hphase
  have hscaled : |largeScale n * ((limitingPhase j (saddleScale α₁ α₂) s).re -
      (limitingPhase j (saddleScale α₁ α₂) ((saddleScale α₁ α₂ : ℂ) * rho j)).re)| ≤
      B * D * (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [abs_mul, abs_of_pos (largeScale_pos hn₀)]
    calc
      _ ≤ largeScale n * (B * (D * smallParameter n)) := mul_le_mul_of_nonneg_left hphase (largeScale_pos hn₀).le
      _ = B * D * (n : ℝ) ^ (1 / 3 : ℝ) := by rw [← largeScale_mul_smallParameter hn₀]; ring
  simp [limitingPhase_saddle j (saddleScale_pos h₁ h₂), Complex.mul_re] at hscaled
  rw [← abs_mul] at hscaled
  obtain ⟨hl₀, hu₀⟩ := abs_le.mp (hn s hs)
  obtain ⟨hl₁, hu₁⟩ := abs_le.mp hscaled
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem uniform_kernel_norm_near_saddle [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖s - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ∃ E : ℝ, |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ = gammaScale α₁ α₂ n *
          Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * largeScale n + E) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_near_saddle h₁ h₂ j hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j] with n hn hdom s hs hdisp
  refine ⟨Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ - Real.log (gammaScale α₁ α₂ n) +
    3 * saddleScale α₁ α₂ * (rho j).re * largeScale n, hn s hs hdisp, ?_⟩
  calc
    _ = Real.exp (Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖) :=
      (Real.exp_log (norm_pos_iff.mpr (kernel_ne_zero j n (hdom.2 hs)))).symm
    _ = Real.exp (Real.log (gammaScale α₁ α₂ n)) *
        Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * largeScale n +
          (Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ - Real.log (gammaScale α₁ α₂ n) +
            3 * saddleScale α₁ α₂ * (rho j).re * largeScale n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := by rw [Real.exp_log (gammaScale_pos h₁ h₂ n)]

/-- The actual simple Gamma saddles have the exponential normalizedKernel size used
as the prefactor in the appendix's Laplace argument. -/
theorem exists_exact_saddle_kernel_norm [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      exactSaddleEquation α₁ α₂ j n s = 0 ∧ deriv (exactSaddleEquation α₁ α₂ j n) s ≠ 0 ∧
      ∃ E : ℝ, |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ = gammaScale α₁ α₂ n *
          Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * largeScale n + E) := by
  obtain ⟨r, _, hr, D, hD, hzeros⟩ := exists_exact_saddle h₁ h₂ j
  obtain ⟨C, hC, hnorm⟩ := uniform_kernel_norm_near_saddle h₁ h₂ j hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [hzeros, hnorm] with n hn he
  obtain ⟨s, hs, hz, hd, hdisp, _⟩ := hn
  exact ⟨s, hr hs, hz, hd, he s (hr hs) hdisp⟩

end ThisWork.Analytic
