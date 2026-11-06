module

public import ThisWork.FiniteContourGap

/-! Integrated exponential estimates on finite contour pieces outside the saddle. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem uniform_moment_compact_integral_gap {α₁ α₂ δ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hδ : 0 < δ) (j : Branch) (M D : ℝ) (k : ℕ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ∀ (a b : ℝ) (v : ℂ) (γ : ℝ → ℂ),
      (∀ u ∈ uIcc a b, γ u ∈ hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
        (saddleContourHeight (saddleScale α₁ α₂) j σ) ∧ ‖γ u‖ ≤ M ∧ δ ≤ ‖γ u - σ‖) →
      ‖∫ u in a..b, v * ((γ u) ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * γ u))‖ ≤
        (‖v‖ * M ^ k * ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
          Real.exp (-ε * largeScale n)) * |b - a| := by
  obtain ⟨ε, hε, hb⟩ := uniform_kernel_compact_gap h₁ h₂ hδ j M D
  refine ⟨ε, hε, hb.mono (fun n hn σ hσ hdisp a b v γ hγ => ?_)⟩
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro u hu
  obtain ⟨htrace, hM, hd⟩ := hγ u (uIoc_subset_uIcc hu)
  calc
    _ = ‖v‖ * (‖γ u‖ ^ k * ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * γ u)‖) := by
      rw [norm_mul, norm_mul, norm_pow]
    _ ≤ ‖v‖ * (M ^ k * (‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
        Real.exp (-ε * largeScale n))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hM k)
          (hn σ hσ hdisp _ htrace hM hd) (norm_nonneg _)
          (pow_nonneg ((norm_nonneg _).trans hM) k)) (norm_nonneg _)
    _ = _ := by ring

end ThisWork
