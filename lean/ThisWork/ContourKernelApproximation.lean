module

public import ThisWork.Argument
public import ThisWork.ContourEquationApproximation
public import ThisWork.LogNorm

/-! Integrating exact-equation errors along pole-free paths. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

noncomputable def kernelPhaseError [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (s : ℂ) : ℝ :=
  Real.log ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ -
    largeScale n * (limitingPhase j (saddleScale α₁ α₂) s).re

theorem hasDerivAt_kernelPhaseError_comp [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) {n : ℕ}
    {γ : ℝ → ℂ} {v : ℂ} {t : ℝ} (hγ : HasDerivAt γ v t)
    (hslit : γ t ∈ Complex.slitPlane)
    (hdom : (largeScale n : ℂ) * γ t ∈ kernelDomain α₁ α₂ n) :
    HasDerivAt (fun u => kernelPhaseError α₁ α₂ j n (γ u))
      (largeScale n * (v * (exactSaddleEquation α₁ α₂ j n (γ t) -
        limitingEquation j (saddleScale α₁ α₂) (γ t))).re) t := by
  have hK := hasDerivAt_log_norm_comp (isOpen_kernelDomain α₁ α₂ n)
    (differentiableOn_kernel α₁ α₂ j n) (fun z hz => kernel_ne_zero j n hz)
    (hγ.const_mul (largeScale n : ℂ)) hdom
  have hφ := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (Neuschel.hasDerivAt_primitive_comp (hasDerivAt_limitingPhase j (saddleScale_pos h₁ h₂)
      ((div_pos_real_mem_slitPlane_iff (saddleScale_pos h₁ h₂) (γ t)).mpr hslit)) hγ)).const_mul (largeScale n)
  convert hK.sub hφ using 1
  · rfl
  · simp only [logDeriv_kernel j n hdom, exactSaddleEquation, Complex.reCLM_apply,
      mul_sub, Complex.sub_re, mul_assoc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]

theorem kernelPhaseError_curve_bound [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) {n : ℕ} (hn : 0 < n)
    {γ : ℝ → ℂ} {v : ℂ} {a b ε : ℝ}
    (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ v t)
    (hslit : ∀ t ∈ uIcc a b, γ t ∈ Complex.slitPlane)
    (hdom : ∀ t ∈ uIcc a b, (largeScale n : ℂ) * γ t ∈ kernelDomain α₁ α₂ n)
    (herr : ∀ t ∈ uIcc a b,
      ‖exactSaddleEquation α₁ α₂ j n (γ t) - limitingEquation j (saddleScale α₁ α₂) (γ t)‖ ≤ ε) :
    |kernelPhaseError α₁ α₂ j n (γ b) - kernelPhaseError α₁ α₂ j n (γ a)| ≤
      largeScale n * ‖v‖ * ε * |b - a| := by
  have hb (t : ℝ) (ht : t ∈ uIcc a b) :
      ‖largeScale n * (v * (exactSaddleEquation α₁ α₂ j n (γ t) -
        limitingEquation j (saddleScale α₁ α₂) (γ t))).re‖ ≤ largeScale n * ‖v‖ * ε := by
    calc
      _ = largeScale n * |(v * (exactSaddleEquation α₁ α₂ j n (γ t) -
          limitingEquation j (saddleScale α₁ α₂) (γ t))).re| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (largeScale_pos hn)]
      _ ≤ largeScale n * ‖v * (exactSaddleEquation α₁ α₂ j n (γ t) -
          limitingEquation j (saddleScale α₁ α₂) (γ t))‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (largeScale_pos hn).le
      _ = largeScale n * ‖v‖ * ‖exactSaddleEquation α₁ α₂ j n (γ t) -
          limitingEquation j (saddleScale α₁ α₂) (γ t)‖ := by rw [norm_mul, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (herr t ht) (mul_nonneg (largeScale_pos hn).le (norm_nonneg _))
  have h := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_kernelPhaseError_comp h₁ h₂ j (hγ t ht) (hslit t ht) (hdom t ht)).hasDerivWithinAt)
    hb left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using h

theorem eventually_bounded_slit_mapsTo_kernelDomain {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ s : ℂ, ‖s‖ ≤ M → s ∈ Complex.slitPlane →
      (largeScale n : ℂ) * s ∈ kernelDomain α₁ α₂ n := by
  filter_upwards [eventually_right_factor_conditions h₁ M,
    eventually_right_factor_conditions h₂ M, eventually_gt_atTop (0 : ℕ)] with n hn₁ hn₂ hn
  refine ⟨hn, fun s hs hslit => ?_⟩
  have hre : ((largeScale n : ℂ) * s).re ≤ largeScale n * M := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans hs) (largeScale_pos hn).le
  change (largeScale n : ℂ) * s ∈ Complex.slitPlane ∧
    ((largeScale n : ℂ) * s).re < min (α₁ * n + 1) (α₂ * n + 1)
  refine ⟨?_, lt_min (by linarith [hn₁.1, hn₁.2]) (by linarith [hn₂.1, hn₂.2])⟩
  rcases Complex.mem_slitPlane_iff.mp hslit with h | h
  · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simpa [Complex.mul_re] using mul_pos (largeScale_pos hn) h))
  · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by
      simpa [Complex.mul_im] using mul_ne_zero (largeScale_pos hn).ne' h))

theorem lineMap_mem_comparison_region {κ η M : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hM : 0 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) (hregion : κ ≤ s.re ∨ η ≤ |s.im|)
    {u : ℝ} (hu : u ∈ Icc 0 1) :
    κ ≤ (AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u).re ∨
      η / 2 ≤ |(AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u).im| := by
  have hRe : (AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u).re =
      (1 - u) * s.re + u * (M + 2 * κ) := by
    simp [AffineMap.lineMap_apply_module, Complex.real_smul, Complex.mul_re]
    ring
  have hIm : (AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u).im = (1 - u) * s.im := by
    simp [AffineMap.lineMap_apply_module, Complex.real_smul, Complex.mul_im]
  by_cases hhalf : 1 / 2 ≤ u
  · left
    rw [hRe]
    have hsr : -M ≤ s.re := (abs_le.mp ((Complex.abs_re_le_norm s).trans hs)).1
    nlinarith [mul_le_mul_of_nonneg_left hsr (show 0 ≤ 1 - u by linarith [hu.2]),
      mul_nonneg (show 0 ≤ 2 * u - 1 by linarith) hM,
      mul_nonneg (show 0 ≤ 2 * u - 1 by linarith) hκ.le]
  rcases hregion with hr | hi
  · left
    rw [hRe]
    nlinarith [mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 - u by linarith [hu.2]),
      mul_nonneg hu.1 (show 0 ≤ M + κ by positivity)]
  · right
    rw [hIm, abs_mul, abs_of_nonneg (show 0 ≤ 1 - u by linarith [hu.2])]
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 - u by linarith [hu.2]),
      mul_nonneg (show 0 ≤ 1 / 2 - u by linarith) hη]

theorem uniform_kernelPhaseError_to_base [PositiveArgument] {α₁ α₂ κ η M ε : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hκ : 0 < κ) (hη : 0 < η)
    (hM : 0 ≤ M) (hε : 0 < ε) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      |kernelPhaseError α₁ α₂ j n s - kernelPhaseError α₁ α₂ j n ((M + 2 * κ : ℝ) : ℂ)| ≤
        ε * largeScale n := by
  have hL : 0 < 2 * M + 2 * κ := by positivity
  filter_upwards [uniform_exactSaddleEquation_region h₁ h₂ hκ (half_pos hη)
    (M := M + 2 * κ) (div_pos hε hL) j,
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
  have hcurve : |kernelPhaseError α₁ α₂ j n ((M + 2 * κ : ℝ) : ℂ) - kernelPhaseError α₁ α₂ j n s| ≤
      largeScale n * ‖((M + 2 * κ : ℝ) : ℂ) - s‖ * (ε / (2 * M + 2 * κ)) := by
    simpa only [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, abs_one, mul_one] using
      kernelPhaseError_curve_bound h₁ h₂ j hF.1
        (γ := fun u : ℝ => AffineMap.lineMap s ((M + 2 * κ : ℝ) : ℂ) u)
        (v := ((M + 2 * κ : ℝ) : ℂ) - s) (a := 0) (b := 1)
        (fun _ _ => AffineMap.hasDerivAt_lineMap) hslit
        (fun u hu => hD.2 _ (hnorm u hu) (hslit u hu))
        (fun u hu => hF.2 _ (hnorm u hu) (hreg u hu))
  have hv : ‖((M + 2 * κ : ℝ) : ℂ) - s‖ ≤ 2 * M + 2 * κ := by
    have h := norm_sub_le ((M + 2 * κ : ℝ) : ℂ) s
    rw [Complex.norm_of_nonneg (show 0 ≤ M + 2 * κ by positivity)] at h
    linarith
  rw [abs_sub_comm]
  calc
    _ ≤ largeScale n * ‖((M + 2 * κ : ℝ) : ℂ) - s‖ * (ε / (2 * M + 2 * κ)) := hcurve
    _ ≤ largeScale n * (2 * M + 2 * κ) * (ε / (2 * M + 2 * κ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (largeScale_pos hF.1).le) (div_pos hε hL).le
    _ = _ := by field_simp [hL.ne']

theorem uniform_kernelPhaseError_difference [PositiveArgument] {α₁ α₂ κ η M ε : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hκ : 0 < κ) (hη : 0 < η)
    (hM : 0 ≤ M) (hε : 0 < ε) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      ∀ t : ℂ, ‖t‖ ≤ M → κ ≤ t.re ∨ η ≤ |t.im| →
      |kernelPhaseError α₁ α₂ j n s - kernelPhaseError α₁ α₂ j n t| ≤ ε * largeScale n := by
  filter_upwards [uniform_kernelPhaseError_to_base h₁ h₂ hκ hη hM (half_pos hε) j]
    with n hn s hs hsr t ht htr
  exact abs_le.mpr ⟨by linarith [(abs_le.mp (hn s hs hsr)).1, (abs_le.mp (hn t ht htr)).2],
    by linarith [(abs_le.mp (hn s hs hsr)).2, (abs_le.mp (hn t ht htr)).1]⟩

end ThisWork.Analytic
