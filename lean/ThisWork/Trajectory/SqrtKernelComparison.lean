module

public import ThisWork.Trajectory.SqrtContourApproximation
public import ThisWork.Trajectory.KernelSaddle
public import ThisWork.ContourKernelApproximation

/-! Uniform comparison of the actual canonical kernel with its square-root phase
on bounded contour pieces. Only differences of logarithmic norms are used. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric Analytic
open scoped Topology

@[expose] noncomputable def kernelPhaseError (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (s : ℂ) : ℝ :=
  Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖ -
    sqrtScale n * (sqrtPhase (doubleSaddleScale d A₁ A₂ z) s).re

theorem hasDerivAt_kernelPhaseError_comp {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) {n : ℕ}
    {γ : ℝ → ℂ} {v : ℂ} {t : ℝ} (hγ : HasDerivAt γ v t)
    (hslit : γ t ∈ Complex.slitPlane)
    (hdom : (sqrtScale n : ℂ) * γ t ∈ Analytic.kernelDomain A₁ A₂ n) :
    HasDerivAt (fun u => kernelPhaseError m d A₁ A₂ z n (γ u))
      (sqrtScale n * (v * (exactSqrtEquation d A₁ A₂ z .three n (γ t) -
        sqrtEquation (doubleSaddleScale d A₁ A₂ z) (γ t))).re) t := by
  have hK := hasDerivAt_log_norm_comp (isOpen_kernelDomain A₁ A₂ n)
    (differentiableOn_kernel hz m d A₁ A₂ .three n) (fun w hw => kernel_ne_zero hz m d .three n hw)
    (hγ.const_mul (sqrtScale n : ℂ)) hdom
  have hφ := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (Neuschel.hasDerivAt_primitive_comp (hasDerivAt_sqrtPhase (doubleSaddleScale_pos hd h₁ h₂ hz)
      ((div_pos_real_mem_slitPlane_iff (doubleSaddleScale_pos hd h₁ h₂ hz) (γ t)).mpr hslit)) hγ)).const_mul (sqrtScale n)
  convert hK.sub hφ using 1
  · rfl
  · simp only [logDeriv_kernel hz m d .three n hdom, exactSqrtEquation, Complex.reCLM_apply,
      mul_sub, Complex.sub_re, mul_assoc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]

theorem kernelPhaseError_curve_bound {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) {n : ℕ} (hn : 0 < n)
    {γ : ℝ → ℂ} {v : ℂ} {a b ε : ℝ}
    (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ v t)
    (hslit : ∀ t ∈ uIcc a b, γ t ∈ Complex.slitPlane)
    (hdom : ∀ t ∈ uIcc a b, (sqrtScale n : ℂ) * γ t ∈ Analytic.kernelDomain A₁ A₂ n)
    (herr : ∀ t ∈ uIcc a b, ‖exactSqrtEquation d A₁ A₂ z .three n (γ t) -
      sqrtEquation (doubleSaddleScale d A₁ A₂ z) (γ t)‖ ≤ ε) :
    |kernelPhaseError m d A₁ A₂ z n (γ b) - kernelPhaseError m d A₁ A₂ z n (γ a)| ≤
      sqrtScale n * ‖v‖ * ε * |b - a| := by
  have hb (t : ℝ) (ht : t ∈ uIcc a b) :
      ‖sqrtScale n * (v * (exactSqrtEquation d A₁ A₂ z .three n (γ t) -
        sqrtEquation (doubleSaddleScale d A₁ A₂ z) (γ t))).re‖ ≤ sqrtScale n * ‖v‖ * ε := by
    calc
      _ = sqrtScale n * |(v * (exactSqrtEquation d A₁ A₂ z .three n (γ t) -
          sqrtEquation (doubleSaddleScale d A₁ A₂ z) (γ t))).re| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (sqrtScale_pos hn)]
      _ ≤ sqrtScale n * ‖v * (exactSqrtEquation d A₁ A₂ z .three n (γ t) -
          sqrtEquation (doubleSaddleScale d A₁ A₂ z) (γ t))‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (sqrtScale_pos hn).le
      _ = sqrtScale n * ‖v‖ * ‖exactSqrtEquation d A₁ A₂ z .three n (γ t) -
          sqrtEquation (doubleSaddleScale d A₁ A₂ z) (γ t)‖ := by rw [norm_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (herr t ht) (mul_nonneg (sqrtScale_pos hn).le (norm_nonneg _))
  have h := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_kernelPhaseError_comp hd h₁ h₂ hz m (hγ t ht) (hslit t ht) (hdom t ht)).hasDerivWithinAt)
    hb left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using h

theorem eventually_bounded_slit_mapsTo_kernelDomain {A₁ A₂ : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ s : ℂ, ‖s‖ ≤ M → s ∈ Complex.slitPlane →
      (sqrtScale n : ℂ) * s ∈ Analytic.kernelDomain A₁ A₂ n := by
  filter_upwards [eventually_right_factor_conditions h₁ M,
    eventually_right_factor_conditions h₂ M, eventually_gt_atTop (0 : ℕ)] with n hn₁ hn₂ hn
  refine ⟨hn, fun s hs hslit => ?_⟩
  have hre : ((sqrtScale n : ℂ) * s).re ≤ sqrtScale n * M := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans hs) (sqrtScale_pos hn).le
  change (sqrtScale n : ℂ) * s ∈ Complex.slitPlane ∧
    ((sqrtScale n : ℂ) * s).re < min (A₁ * n + 1) (A₂ * n + 1)
  refine ⟨?_, lt_min (by linarith [hn₁.1, hn₁.2]) (by linarith [hn₂.1, hn₂.2])⟩
  rcases Complex.mem_slitPlane_iff.mp hslit with h | h
  · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simpa [Complex.mul_re] using mul_pos (sqrtScale_pos hn) h))
  · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by
      simpa [Complex.mul_im] using mul_ne_zero (sqrtScale_pos hn).ne' h))

theorem uniform_kernelPhaseError_to_base {d : ℕ} {A₁ A₂ z κ η M ε : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ)
    (hκ : 0 < κ) (hη : 0 < η) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      |kernelPhaseError m d A₁ A₂ z n s -
        kernelPhaseError m d A₁ A₂ z n ((M + 2 * κ : ℝ) : ℂ)| ≤ ε * sqrtScale n := by
  have hL : 0 < 2 * M + 2 * κ := by positivity
  filter_upwards [uniform_exactSqrtEquation_region hd h₁ h₂ hz hκ (half_pos hη)
    (M := M + 2 * κ) (div_pos hε hL) .three,
    eventually_bounded_slit_mapsTo_kernelDomain h₁ h₂ (M + 2 * κ)]
    with n hF hD s hs hregion
  have hnorm : ∀ u ∈ uIcc (0 : ℝ) 1,
      ‖AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u‖ ≤ M + 2 * κ := by
    intro u hu
    have hmem := (convex_closedBall (0 : ℂ) (M + 2 * κ)).lineMap_mem
      (show s ∈ closedBall (0 : ℂ) (M + 2 * κ) by
        simpa only [mem_closedBall, dist_zero_right] using hs.trans (show M ≤ M + 2 * κ by linarith))
      (show ((M + 2 * κ : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (M + 2 * κ) by
        simp only [mem_closedBall, dist_zero_right]
        rw [Complex.norm_of_nonneg (show 0 ≤ M + 2 * κ by positivity)])
      (show u ∈ Icc (0 : ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using hu)
    simpa only [mem_closedBall, dist_zero_right] using hmem
  have hreg : ∀ u ∈ uIcc (0 : ℝ) 1,
      κ ≤ (AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u).re ∨
        η / 2 ≤ |(AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u).im| :=
    fun u hu => lineMap_mem_comparison_region hκ hη.le hM hs hregion
      (by simpa only [uIcc_of_le zero_le_one] using hu)
  have hslit : ∀ u ∈ uIcc (0 : ℝ) 1,
      AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u ∈ Complex.slitPlane := by
    intro u hu
    rcases hreg u hu with hre | him
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (hκ.trans_le hre))
    · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by intro he; rw [he, abs_zero] at him; linarith))
  have hcurve : |kernelPhaseError m d A₁ A₂ z n ((M + 2 * κ : ℝ) : ℂ) - kernelPhaseError m d A₁ A₂ z n s| ≤
      sqrtScale n * ‖((M + 2 * κ : ℝ) : ℂ) - s‖ * (ε / (2 * M + 2 * κ)) := by
    simpa only [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, abs_one, mul_one] using
      kernelPhaseError_curve_bound hd h₁ h₂ hz m hF.1
        (γ := fun u : ℝ => AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u)
        (v := ((M + 2 * κ : ℝ) : ℂ) - s) (a := 0) (b := 1)
        (fun _ _ => AffineMap.hasDerivAt_lineMap) hslit
        (fun u hu => hD.2 _ (hnorm u hu) (hslit u hu))
        (fun u hu => by
          simpa only [limitingSqrtEquation, twist_three, add_zero] using
            hF.2 _ (hnorm u hu) (hreg u hu))
  have hv : ‖((M + 2 * κ : ℝ) : ℂ) - s‖ ≤ 2 * M + 2 * κ := by
    have h := norm_sub_le ((M + 2 * κ : ℝ) : ℂ) s
    rw [Complex.norm_of_nonneg (show 0 ≤ M + 2 * κ by positivity)] at h
    linarith
  rw [abs_sub_comm]
  calc
    _ ≤ sqrtScale n * ‖((M + 2 * κ : ℝ) : ℂ) - s‖ * (ε / (2 * M + 2 * κ)) := hcurve
    _ ≤ sqrtScale n * (2 * M + 2 * κ) * (ε / (2 * M + 2 * κ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (sqrtScale_pos hF.1).le) (div_pos hε hL).le
    _ = _ := by field_simp [hL.ne']

theorem uniform_kernelPhaseError_difference {d : ℕ} {A₁ A₂ z κ η M ε : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ)
    (hκ : 0 < κ) (hη : 0 < η) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      ∀ t : ℂ, ‖t‖ ≤ M → κ ≤ t.re ∨ η ≤ |t.im| →
      |kernelPhaseError m d A₁ A₂ z n s - kernelPhaseError m d A₁ A₂ z n t| ≤ ε * sqrtScale n := by
  filter_upwards [uniform_kernelPhaseError_to_base hd h₁ h₂ hz m hκ hη hM (half_pos hε)]
    with n hn s hs hsr t ht htr
  exact abs_le.mpr ⟨by linarith [(abs_le.mp (hn s hs hsr)).1, (abs_le.mp (hn t ht htr)).2],
    by linarith [(abs_le.mp (hn s hs hsr)).2, (abs_le.mp (hn t ht htr)).1]⟩

end ThisWork.Trajectory
