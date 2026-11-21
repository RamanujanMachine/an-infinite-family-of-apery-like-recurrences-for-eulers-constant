module

public import ThisWork.Trajectory.SqrtKernelComparison
public import ThisWork.Trajectory.SqrtSaddleDisk
public import ThisWork.FiniteContourGap

/-! Uniform global phase gaps on bounded moving canonical contours. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric Analytic
open scoped Topology

theorem exists_uniform_sqrt_phase_gap {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (M D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ : ℂ, ‖σ - (c : ℂ)‖ ≤ D / sqrtScale n →
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight c .three σ) (saddleContourHeight c .three σ) →
        ‖s‖ ≤ M → δ ≤ ‖s - σ‖ → ε ≤ (sqrtPhase c σ).re - (sqrtPhase c s).re := by
  obtain ⟨ε, hε, hp⟩ := exists_uniform_perturbed_limiting_gap hc hδ .three M
  simp only [rho_three, mul_one] at hp
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hp
  have hsmall : ∀ᶠ n : ℕ in atTop, D / sqrtScale n < r :=
    (show Tendsto (fun n => D / sqrtScale n) atTop (𝓝 0) by
      simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
        (tendsto_inv_atTop_zero.comp sqrtScale_tendsto).const_mul D).eventually (gt_mem_nhds hr)
  refine ⟨ε / 3, by positivity, ?_⟩
  filter_upwards [hsmall] with n hn σ hσ s hs hM hd
  have h := hball σ (by simpa only [mem_ball, dist_eq_norm] using hσ.trans_lt hn) s hs hM hd
  simp [sqrtPhase, Complex.mul_re]
  linarith

theorem uniform_log_kernel_compact_gap {d : ℕ} {A₁ A₂ z δ : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hδ : 0 < δ)
    (m : ℕ) (M D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
        (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ) →
      ‖s‖ ≤ M → δ ≤ ‖s - σ‖ →
      ε * sqrtScale n ≤ Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ -
        Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖ := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_sqrt_phase_gap hc hδ M D
  have hcmp := uniform_kernelPhaseError_difference hd h₁ h₂ hz m
    (κ := c / 4) (η := c / 4) (M := max M (2 * c)) (by positivity) (by positivity)
    ((show 0 ≤ 2 * c by positivity).trans (le_max_right _ _)) (half_pos hε)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [hgap, hcmp, eventually_gt_atTop (0 : ℕ)] with n hg he hn σ hσ hdisp s hs hM hdist
  have hσM : ‖σ‖ ≤ max M (2 * c) :=
    (saddleDisk_norm_le hc .three hσ).trans ((show 5 * c / 4 ≤ 2 * c by linarith).trans (le_max_right _ _))
  have herr := he σ hσM (saddleDisk_mem_comparison_region hc .three hσ)
    s (hM.trans (le_max_left _ _)) (saddleContour_mem_region hc .three hσ hs)
  have hlim := mul_le_mul_of_nonneg_left (hg σ hdisp s hs hM hdist) (sqrtScale_pos hn).le
  dsimp only [kernelPhaseError, c] at herr hlim ⊢
  nlinarith [(abs_le.mp herr).1]

/-- Every bounded portion outside a fixed saddle window is exponentially smaller
than the actual canonical saddle kernel. -/
theorem uniform_kernel_compact_gap {d : ℕ} {A₁ A₂ z δ : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hδ : 0 < δ)
    (m : ℕ) (M D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
        (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ) →
      ‖s‖ ≤ M → δ ≤ ‖s - σ‖ →
      ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖ ≤
        ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n) := by
  obtain ⟨ε, hε, hb⟩ := uniform_log_kernel_compact_gap hd h₁ h₂ hz hδ m M D
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hb, eventually_sqrtDisk_mapsTo_kernelDomain h₁ h₂
    (doubleSaddleScale_pos hd h₁ h₂ hz)] with n hn hdom σ hσ hdisp s hs hM hdist
  calc
    _ ≤ Real.exp (Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ + (-ε * sqrtScale n)) :=
      Real.exp_le_exp.mpr (by linarith [hn σ hσ hdisp s hs hM hdist])
    _ = _ := by rw [Real.exp_add, Real.exp_log
      (norm_pos_iff.mpr (kernel_ne_zero hz m d .three n (hdom.2 hσ)))]

end ThisWork.Trajectory
