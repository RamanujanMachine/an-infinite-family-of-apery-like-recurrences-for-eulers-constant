module

public import ThisWork.Argument
public import ThisWork.UniformNormalizedTails

/-! Uniform saddle-normalized tail bounds for the actual vector components. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem norm_scaled_polynomial_left_le {R t y H : ℝ} {n : ℕ}
    (hR : 0 ≤ R) (hRn : R ≤ n) (ht : 0 ≤ t) (hy : |y| ≤ H) :
    ‖(n : ℂ) - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (n : ℝ) * (1 + t + H) := by
  have hs : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ t + H := by
    simpa only [Nat.cast_zero, zero_sub, norm_neg, zero_add] using norm_polynomial_left_le ht hy 0
  calc
    _ ≤ ‖(n : ℂ)‖ + ‖(R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ := norm_sub_le _ _
    _ = (n : ℝ) + R * ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ := by
      rw [norm_mul, Complex.norm_of_nonneg hR, Complex.norm_natCast]
    _ ≤ (n : ℝ) + n * ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hRn (norm_nonneg _))
    _ ≤ (n : ℝ) + n * (t + H) := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
    _ = _ := by ring

theorem uniform_weighted_kernel_normalized_far_tail [PositiveArgument] {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H)
    (j : Branch) (k : ℕ) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ t : ℝ, T ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖((n : ℂ) - (largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) ^ k *
        normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        (n : ℝ) ^ k * ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
          Real.exp (-q * largeScale n * t) := by
  obtain ⟨T, hT, hb⟩ := uniform_kernel_normalized_far_tail h₁ h₂ hη hH j (q + 1)
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (eventually_shifted_pow_le_exp (D := H + 1) (by positivity) k)
  refine ⟨max T A, hT.trans (le_max_left _ _), ?_⟩
  filter_upwards [hb, largeScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hn hR hn₁ σ hσ t ht y hy hyH
  have ht₁ : 1 ≤ t := hT.trans ((le_max_left _ _).trans ht)
  have hRn : largeScale n ≤ (n : ℝ) :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hn₁) (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hp : ‖(n : ℂ) - (largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ ^ k ≤
      (n : ℝ) ^ k * Real.exp t := by
    calc
      _ ≤ ((n : ℝ) * (1 + t + H)) ^ k := pow_le_pow_left₀ (norm_nonneg _)
        (norm_scaled_polynomial_left_le (by linarith) hRn (by linarith) hyH) k
      _ = (n : ℝ) ^ k * (t + (H + 1)) ^ k := by
        rw [show 1 + t + H = t + (H + 1) by ring, mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hA t ((le_max_right _ _).trans ht)) (by positivity)
  calc
    _ = ‖(n : ℂ) - (largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ ^ k *
        ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ := by rw [norm_mul, norm_pow]
    _ ≤ ((n : ℝ) ^ k * Real.exp t) *
        (‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-(q + 1) * largeScale n * t)) :=
      mul_le_mul hp (hn σ hσ t ((le_max_left _ _).trans ht) y hy hyH) (norm_nonneg _) (by positivity)
    _ = ((n : ℝ) ^ k * ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖) *
        Real.exp (t + (-(q + 1) * largeScale n * t)) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_right hR (show 0 ≤ t by linarith)])) (by positivity)

end ThisWork.Analytic
