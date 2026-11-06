module

public import ThisWork.ContourKernelApproximation

/-! Uniform gaps for the actual finite-index kernel on bounded moving contours. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem saddleDisk_mem_comparison_region {c : ℝ} (hc : 0 < c) (j : Branch) {σ : ℂ}
    (hσ : σ ∈ saddleDisk c j) : c / 4 ≤ σ.re ∨ c / 4 ≤ |σ.im| := by
  have h := saddleDisk_region hc j hσ
  cases j
  · exact Or.inr h.2
  · exact Or.inr h.2
  · exact Or.inl (by change c / 2 ≤ σ.re at h; linarith)

theorem uniform_log_kernel_compact_gap {α₁ α₂ δ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hδ : 0 < δ) (j : Branch) (M D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
        (saddleContourHeight (saddleScale α₁ α₂) j σ) →
      ‖s‖ ≤ M → δ ≤ ‖s - σ‖ →
      ε * largeScale n ≤ Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ -
        Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ := by
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_limiting_gap_near_exact_saddles h₁ h₂ hδ j M D
  have hc := saddleScale_pos h₁ h₂
  have hcmp := uniform_kernelPhaseError_difference h₁ h₂
    (κ := saddleScale α₁ α₂ / 4) (η := saddleScale α₁ α₂ / 4)
    (M := max M (2 * saddleScale α₁ α₂)) (by positivity) (by positivity)
    ((show 0 ≤ 2 * saddleScale α₁ α₂ by positivity).trans (le_max_right _ _)) (half_pos hε) j
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [hgap, hcmp, eventually_gt_atTop (0 : ℕ)]
    with n hg he hn σ hσ hdisp s hs hM hd
  have hσM : ‖σ‖ ≤ max M (2 * saddleScale α₁ α₂) :=
    (saddleDisk_norm_le hc j hσ).trans ((show 5 * saddleScale α₁ α₂ / 4 ≤ 2 * saddleScale α₁ α₂
      by linarith).trans (le_max_right _ _))
  have herr := he σ hσM (saddleDisk_mem_comparison_region hc j hσ)
    s (hM.trans (le_max_left _ _)) (saddleContour_mem_region hc j hσ hs)
  dsimp only [kernelPhaseError] at herr
  nlinarith [(abs_le.mp herr).1,
    mul_le_mul_of_nonneg_left (hg σ hdisp s hs hM hd) (largeScale_pos hn).le]

/-- The actual finite-index kernel is exponentially smaller than its saddle
value on every bounded contour piece a fixed distance from the moving saddle. -/
theorem uniform_kernel_compact_gap {α₁ α₂ δ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hδ : 0 < δ) (j : Branch) (M D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
        (saddleContourHeight (saddleScale α₁ α₂) j σ) →
      ‖s‖ ≤ M → δ ≤ ‖s - σ‖ →
      ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ ≤
        ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-ε * largeScale n) := by
  obtain ⟨ε, hε, hb⟩ := uniform_log_kernel_compact_gap h₁ h₂ hδ j M D
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hb, eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j]
    with n hn hdom σ hσ hdisp s hs hM hd
  calc
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ + (-ε * largeScale n)) :=
      Real.exp_le_exp.mpr (by linarith [hn σ hσ hdisp s hs hM hd])
    _ = _ := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr (kernel_ne_zero j n (hdom.2 hσ)))]

end ThisWork
