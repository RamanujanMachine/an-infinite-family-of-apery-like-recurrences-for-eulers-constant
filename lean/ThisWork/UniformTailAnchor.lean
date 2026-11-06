module

public import ThisWork.UniformTailDecay

/-! Uniform bounds at fixed left-tail anchors. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem isCompact_heightStrip (η H : ℝ) : IsCompact {y : ℝ | η ≤ |y| ∧ |y| ≤ H} := by
  exact isCompact_Icc.of_isClosed_subset
    ((isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const))
    (fun y hy => abs_le.mp hy.2)

theorem limitingPhase_left_anchor_bounded {c η H : ℝ} (hc : 0 < c) (hη : 0 < η) (j : Branch) :
    ∃ B ≥ 0, ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      (limitingPhase j c (-1 + (y : ℂ) * Complex.I)).re ≤ B := by
  have hcont : ContinuousOn (fun y : ℝ => limitingPhase j c (-1 + (y : ℂ) * Complex.I))
      {y : ℝ | η ≤ |y| ∧ |y| ≤ H} :=
    (differentiableOn_limitingPhase j hc).continuousOn.comp (by fun_prop)
      (fun y hy => Complex.mem_slitPlane_iff.mpr (Or.inr (by
        have hy₀ : y ≠ 0 := by intro h; have hbad := hy.1; rw [h, abs_zero] at hbad; linarith
        simpa using hy₀)))
  obtain ⟨B, hB⟩ := (isCompact_heightStrip η H).exists_bound_of_continuousOn hcont
  exact ⟨max B 0, le_max_right _ _, fun y hy hyH =>
    ((Complex.re_le_norm _).trans (hB y ⟨hy, hyH⟩)).trans (le_max_left _ _)⟩

theorem uniform_gammaNormError_left_anchor {η H : ℝ} (hη : 0 < η) (hH : 0 ≤ H) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      |gammaNormError ((largeScale n : ℂ) * (-1 + (y : ℂ) * Complex.I))| ≤
        C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := uniform_scaled_gammaNormError_left zero_lt_one hη
    (show 0 < 1 + H by positivity)
  have he := gammaNormError_rate_of_scaled_bound
    (K := {s : ℂ | s.re = -1 ∧ η ≤ |s.im| ∧ |s.im| ≤ H}) hC
    (hb.mono fun R hR s hs => hR.2 s
      (by have hn := Complex.norm_le_abs_re_add_abs_im s; rw [hs.1, abs_neg, abs_one] at hn; linarith [hs.2.2])
      hs.1.le hs.2.1)
  obtain ⟨D, hD, hbD⟩ := he
  exact ⟨D, hD, hbD.mono fun n hn y hy hyH =>
    hn _ (by simpa using (show (-1 : ℝ) = -1 ∧ η ≤ |y| ∧ |y| ≤ H from ⟨rfl, hy, hyH⟩))⟩

theorem norm_left_anchor_le {y H : ℝ} (hy : |y| ≤ H) :
    ‖(-1 : ℂ) + (y : ℂ) * Complex.I‖ ≤ 1 + H := by
  calc
    _ ≤ ‖(-1 : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = 1 + |y| := by simp
    _ ≤ 1 + H := add_le_add (le_refl _) hy

theorem uniform_log_norm_kernel_left_anchor {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (j : Branch) :
    ∃ B ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-1 + (y : ℂ) * Complex.I))‖ -
        Real.log (gammaScale α₁ α₂ n) ≤ B * largeScale n := by
  obtain ⟨C₀, hC₀, hb₀⟩ := uniform_gammaNormError_left_anchor hη hH
  obtain ⟨C₁, hC₁, hb₁⟩ := uniform_log_norm_Gamma_affine h₁ (show 0 < 1 + H by positivity)
  obtain ⟨C₂, hC₂, hb₂⟩ := uniform_log_norm_Gamma_affine h₂ (show 0 < 1 + H by positivity)
  obtain ⟨B, hB, hphase⟩ := limitingPhase_left_anchor_bounded (H := H) (saddleScale_pos h₁ h₂) hη j
  refine ⟨B + 3 * C₀ + C₁ + C₂, by positivity, ?_⟩
  filter_upwards [hb₀, hb₁, hb₂, eventually_ge_atTop (1 : ℕ)] with n hn₀ hn₁ hn₂ hn y hy hyH
  have hx := scaled_left_mem_kernelDomain h₁ h₂ n (largeScale_pos (by omega : 0 < n))
    (t := 1) zero_lt_one (y := y) (by intro h; rw [h, abs_zero] at hy; linarith)
  have he := log_norm_kernel_error h₁ h₂ j (by omega : 0 < n)
    (s := -1 + (y : ℂ) * Complex.I)
    (by intro h; have hr := congrArg Complex.re h; norm_num [Complex.mul_re] at hr)
    (by simpa using hx)
  have he₁ : |rightGammaNormError α₁ n (-1 + (y : ℂ) * Complex.I)| ≤ C₁ * (n : ℝ) ^ (1 / 3 : ℝ) :=
    hn₁ _ (norm_left_anchor_le hyH)
  have he₂ : |rightGammaNormError α₂ n (-1 + (y : ℂ) * Complex.I)| ≤ C₂ * (n : ℝ) ^ (1 / 3 : ℝ) :=
    hn₂ _ (norm_left_anchor_le hyH)
  have hp : (n : ℝ) ^ (1 / 3 : ℝ) ≤ largeScale n :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)
  nlinarith [hn₀ y hy hyH, le_abs_self (gammaNormError ((largeScale n : ℂ) * (-1 + (y : ℂ) * Complex.I))),
    (abs_le.mp he₁).2, (abs_le.mp he₂).2,
    mul_le_mul_of_nonneg_left (hphase y hy hyH) (largeScale_pos (by omega : 0 < n)).le,
    mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * C₀ + C₁ + C₂ by positivity)]

/-- Absolute logarithmic tail control normalized by the actual Gamma scale,
with one constant and index threshold uniform on both horizontal tails. -/
theorem uniform_log_norm_kernel_left_tail {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (j : Branch) :
    ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ -
        Real.log (gammaScale α₁ α₂ n) ≤ largeScale n * (-t * Real.log t + D * t) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_tail_difference (H := H) h₁ h₂ hη j
  obtain ⟨B, hB, ha⟩ := uniform_log_norm_kernel_left_anchor (H := H) h₁ h₂ hη hH j
  refine ⟨B + C + 1, by positivity, ?_⟩
  filter_upwards [hb, ha, eventually_gt_atTop (0 : ℕ)] with n hn hanchor hn₀ t ht y hy hyH
  have h := hn 1 le_rfl t ht y hy hyH
  simp only [Complex.ofReal_one, Real.log_one, mul_zero, sub_zero] at h
  nlinarith [hanchor y hy hyH, (largeScale_pos hn₀).le,
    mul_nonneg (mul_nonneg hB (largeScale_pos hn₀).le) (show 0 ≤ t - 1 by linarith)]

theorem uniform_kernel_left_tail_bound {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (j : Branch) :
    ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        gammaScale α₁ α₂ n * Real.exp (largeScale n * (-t * Real.log t + D * t)) := by
  obtain ⟨D, hD, hb⟩ := uniform_log_norm_kernel_left_tail h₁ h₂ hη hH j
  refine ⟨D, hD, hb.mono fun n hn t ht y hy hyH => ?_⟩
  calc
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n
        ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log (gammaScale α₁ α₂ n) + largeScale n * (-t * Real.log t + D * t)) :=
      Real.exp_le_exp.mpr (by linarith [hn t ht y hy hyH])
    _ = _ := by rw [Real.exp_add, Real.exp_log (gammaScale_pos h₁ h₂ n)]

end ThisWork
