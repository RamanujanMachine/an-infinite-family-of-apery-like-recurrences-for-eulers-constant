module

public import ThisWork.Argument
public import ThisWork.IntegratedTails

/-! Uniform infinite-tail bounds for the scaled power moments used for independence. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable def scaledLeftMomentKernel [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n k : ℕ)
    (y t : ℝ) : ℂ :=
  (-(t : ℂ) + (y : ℂ) * Complex.I) ^ k *
    normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))

theorem uniform_moment_normalized_far_tail [PositiveArgument] {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H)
    (j : Branch) (k : ℕ) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ t : ℝ, T ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖scaledLeftMomentKernel α₁ α₂ j n k y t‖ ≤
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-q * largeScale n * t) := by
  obtain ⟨T, hT, hb⟩ := uniform_kernel_normalized_far_tail h₁ h₂ hη hH j (q + 1)
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (eventually_shifted_pow_le_exp (D := H + 1) (by positivity) k)
  refine ⟨max T A, hT.trans (le_max_left _ _), ?_⟩
  filter_upwards [hb, largeScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hR σ hσ t ht y hy hyH
  have ht₁ : 1 ≤ t := hT.trans ((le_max_left _ _).trans ht)
  have hs : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ t + H := by
    simpa only [Nat.cast_zero, zero_sub, norm_neg, zero_add] using
      norm_polynomial_left_le (show 0 ≤ t by linarith) hyH 0
  have hp : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ^ k ≤ Real.exp t :=
    (pow_le_pow_left₀ (norm_nonneg _) (hs.trans (by linarith : t + H ≤ t + (H + 1))) k).trans
      (hA t ((le_max_right _ _).trans ht))
  calc
    _ = ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ^ k *
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ := by
      rw [scaledLeftMomentKernel, norm_mul, norm_pow]
    _ ≤ Real.exp t * (‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
        Real.exp (-(q + 1) * largeScale n * t)) :=
      mul_le_mul hp (hn σ hσ t ((le_max_left _ _).trans ht) y hy hyH) (norm_nonneg _) (by positivity)
    _ = ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
        Real.exp (t + (-(q + 1) * largeScale n * t)) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hR (show 0 ≤ t by linarith)])) (norm_nonneg _)

theorem uniform_integrated_moment_tail_cutoffs [PositiveArgument] {α₁ α₂ η H q : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (hq : 0 < q)
    (j : Branch) (k : ℕ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ A : ℝ, T ≤ A → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      IntegrableOn (scaledLeftMomentKernel α₁ α₂ j n k y) (Ioi A) ∧
      ‖∫ t in Ioi A, scaledLeftMomentKernel α₁ α₂ j n k y t‖ ≤
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
          Real.exp (-q * largeScale n * A) / (q * largeScale n) := by
  obtain ⟨T, hT, hb⟩ := uniform_moment_normalized_far_tail h₁ h₂ hη hH j k q
  refine ⟨T, hT, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 σ hσ A hA y hy hyH
  have hy0 : y ≠ 0 := by intro he; simp only [he, abs_zero] at hy; linarith
  have hcurve : Continuous (fun t : ℝ =>
      (largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hc := (differentiableOn_kernel α₁ α₂ j n).continuousOn.comp
    (s := Ioi A) hcurve.continuousOn
    (fun t ht => scaled_left_mem_kernelDomain h₁ h₂ n (largeScale_pos hn0)
      (lt_of_lt_of_le zero_lt_one (hT.trans (hA.trans ht.le))) hy0)
  have hpoly : Continuous (fun t : ℝ => (-(t : ℂ) + (y : ℂ) * Complex.I) ^ k) := by fun_prop
  have hfc := hpoly.continuousOn.mul hc
  change ContinuousOn (scaledLeftMomentKernel α₁ α₂ j n k y) (Ioi A) at hfc
  simpa only [neg_mul] using integral_norm_le_exp_tail
    (mul_pos hq (largeScale_pos hn0)) (hfc.aestronglyMeasurable measurableSet_Ioi)
    (fun t ht => by simpa only [neg_mul] using hn σ hσ t (hA.trans ht.le) y hy hyH)

theorem uniform_integrated_moment_tail [PositiveArgument] {α₁ α₂ η H q : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (hq : 0 < q)
    (j : Branch) (k : ℕ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      IntegrableOn (scaledLeftMomentKernel α₁ α₂ j n k y) (Ioi T) ∧
      ‖∫ t in Ioi T, scaledLeftMomentKernel α₁ α₂ j n k y t‖ ≤
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
          Real.exp (-q * largeScale n * T) / (q * largeScale n) := by
  obtain ⟨T, hT, hb⟩ := uniform_integrated_moment_tail_cutoffs h₁ h₂ hη hH hq j k
  exact ⟨T, hT, hb.mono (fun _ hn σ hσ y hy hyH => hn σ hσ T le_rfl y hy hyH)⟩

end ThisWork.Analytic
