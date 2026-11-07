module

public import ThisWork.Argument
public import ThisWork.SaddleDisks
public import ThisWork.SaddleStability

/-! Existence, simplicity, uniqueness and displacement of the exact Gamma saddles. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

/-- Step 1 of Appendix A: for each branch, the actual scaled Gamma-product
equation has a unique simple zero in a fixed neighborhood of its limiting zero,
with displacement bounded by a constant times `n^(-1/3)`. -/
theorem exists_exact_saddle [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ r > 0, ball ((saddleScale α₁ α₂ : ℂ) * rho j) r ⊆ saddleDisk (saddleScale α₁ α₂) j ∧
      ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
        ∃ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) r,
          exactSaddleEquation α₁ α₂ j n s = 0 ∧
          deriv (exactSaddleEquation α₁ α₂ j n) s ≠ 0 ∧
          ‖s - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ C * smallParameter n ∧
          ∀ t ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) r,
            exactSaddleEquation α₁ α₂ j n t = 0 → t = s := by
  let c := saddleScale α₁ α₂
  have hc : 0 < c := saddleScale_pos h₁ h₂
  have hf : DifferentiableOn ℂ (limitingEquation j c) (ball ((c : ℂ) * rho j) (c / 4)) :=
    differentiableOn_limitingEquation_disk hc j
  obtain ⟨C, hC, hb⟩ := uniform_exactSaddleEquation_disk h₁ h₂ j
  have ha : (c : ℂ) * rho j ∈ ball ((c : ℂ) * rho j) (c / 4) := mem_ball_self (by positivity)
  obtain ⟨r, hr, hrG, K, hK, hzeros⟩ := exists_simple_zero_with_rate (ε := smallParameter) isOpen_ball ha
    (eventually_differentiableOn_exactSaddleEquation h₁ h₂ j) hf
    (((exactSaddleEquation_tendsto_uniform_disk h₁ h₂ j).mono ball_subset_closedBall).tendstoLocallyUniformlyOn)
    (limitingEquation_saddle j hc) (limitingEquation_saddle_simple j hc) hC
    (hb.mono (fun n hn => by
      simpa only [c, limitingEquation_saddle j (saddleScale_pos h₁ h₂), sub_zero] using
        hn _ (ball_subset_closedBall ha)))
  exact ⟨r, hr, fun s hs => ball_subset_closedBall (hrG hs), K, hK, hzeros⟩

/-- These are stationary points of the original Gamma-product normalizedKernel, with the
scaled equation simple and the displacement estimate from the appendix. -/
theorem exists_exact_kernel_saddle [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      (largeScale n : ℂ) * s ∈ kernelDomain α₁ α₂ n ∧
      deriv (normalizedKernel α₁ α₂ j n) ((largeScale n : ℂ) * s) = 0 ∧
      deriv (exactSaddleEquation α₁ α₂ j n) s ≠ 0 ∧
      ‖s - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ C * smallParameter n := by
  obtain ⟨r, hr, hrD, C, hC, hn⟩ := exists_exact_saddle h₁ h₂ j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hn, eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j] with n hn hdom
  obtain ⟨s, hs, hz, hd, he, _⟩ := hn
  exact ⟨s, hrD hs, hdom.2 (hrD hs),
    (kernelLogDerivative_eq_zero_iff j n (hdom.2 (hrD hs))).mp hz, hd, he⟩

end ThisWork.Analytic
