module

public import ThisWork.UniformTailAnchor

/-! Uniform tail estimates relative to the actual moving saddle prefactor. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem limitingPhase_saddleDisk_bounded {c : ℝ} (hc : 0 < c) (j : Branch) :
    ∃ B ≥ 0, ∀ s ∈ saddleDisk c j, ‖limitingPhase j c s‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall ((c : ℂ) * rho j) (c / 4)).exists_bound_of_continuousOn
    ((differentiableOn_limitingPhase j hc).continuousOn.mono (fun s hs => saddleDisk_mem_slitPlane hc j hs))
  exact ⟨max B 0, le_max_right _ _, fun s hs => (hB s hs).trans (le_max_left _ _)⟩

theorem uniform_log_norm_kernel_saddleDisk_lower {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      -D * largeScale n ≤ Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * s)‖ -
        Real.log (gammaScale α₁ α₂ n) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_disk h₁ h₂ j
  obtain ⟨B, hB, hphase⟩ := limitingPhase_saddleDisk_bounded (saddleScale_pos h₁ h₂) j
  refine ⟨B + C, by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn₁ s hs
  have hp : (n : ℝ) ^ (1 / 3 : ℝ) ≤ largeScale n :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn₁) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)
  nlinarith [(abs_le.mp (hn s hs)).1, mul_le_mul_of_nonneg_left hp hC,
    mul_le_mul_of_nonneg_left ((abs_le.mp ((Complex.abs_re_le_norm _).trans (hphase s hs))).1)
      (largeScale_pos (by omega : 0 < n)).le]

theorem uniform_log_norm_kernel_normalized_tail {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (j : Branch) :
    ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ -
        Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ ≤
        largeScale n * (-t * Real.log t + D * t) := by
  obtain ⟨D, hD, hb⟩ := uniform_log_norm_kernel_left_tail h₁ h₂ hη hH j
  obtain ⟨B, hB, hsaddle⟩ := uniform_log_norm_kernel_saddleDisk_lower h₁ h₂ j
  refine ⟨D + B, by positivity, ?_⟩
  filter_upwards [hb, hsaddle, eventually_gt_atTop (0 : ℕ)] with n hn hs hn₀ σ hσ t ht y hy hyH
  nlinarith [hn t ht y hy hyH, hs σ hσ,
    mul_nonneg (mul_nonneg hB (largeScale_pos hn₀).le) (show 0 ≤ t - 1 by linarith)]

theorem uniform_kernel_normalized_far_tail {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (j : Branch) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ t : ℝ, T ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-q * largeScale n * t) := by
  obtain ⟨D, hD, hb⟩ := uniform_log_norm_kernel_normalized_tail h₁ h₂ hη hH j
  refine ⟨Real.exp (D + q) + 1, by linarith [Real.exp_pos (D + q)], ?_⟩
  filter_upwards [hb, eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j]
    with n hn hdom σ hσ t ht y hy hyH
  have ht₁ : 1 ≤ t := by linarith [Real.exp_pos (D + q)]
  have hl : D + q ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (D + q))
      (show Real.exp (D + q) ≤ t by linarith)
  calc
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n
        ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ + (-q * largeScale n * t)) :=
      Real.exp_le_exp.mpr (by nlinarith [hn σ hσ t ht₁ y hy hyH,
        mul_le_mul_of_nonneg_left hl (mul_nonneg (largeScale_pos hdom.1).le (show 0 ≤ t by linarith))])
    _ = _ := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr (kernel_ne_zero j n (hdom.2 hσ)))]

end ThisWork
