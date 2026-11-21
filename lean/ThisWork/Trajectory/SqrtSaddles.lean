module

public import ThisWork.Trajectory.SqrtSaddleDisk
public import ThisWork.SaddleStability

/-! The actual canonical Gamma saddle has square-root size and a quadratic phase. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

theorem exists_exact_sqrt_saddle {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ r > 0, ball (doubleSaddleScale d A₁ A₂ z : ℂ) r ⊆
      ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) ∧
      ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
        ∃ s ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) r,
          exactSqrtEquation d A₁ A₂ z .three n s = 0 ∧
          deriv (exactSqrtEquation d A₁ A₂ z .three n) s ≠ 0 ∧
          ‖s - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ C / sqrtScale n ∧
          ∀ t ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) r,
            exactSqrtEquation d A₁ A₂ z .three n t = 0 → t = s := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  have ha : (c : ℂ) ∈ ball (c : ℂ) (c / 4) := mem_ball_self (by positivity)
  obtain ⟨C, hC, hb⟩ := uniform_exactSqrtEquation_disk hd h₁ h₂ hz
  have hlim : TendstoUniformlyOn (fun n => exactSqrtEquation d A₁ A₂ z .three n)
      (sqrtEquation c) atTop (ball (c : ℂ) (c / 4)) :=
    (exactSqrtEquation_tendsto_uniform_disk hd h₁ h₂ hz).mono fun s hs => by
      simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs
  have hcenter : ∀ᶠ n : ℕ in atTop,
      ‖exactSqrtEquation d A₁ A₂ z .three n (c : ℂ)‖ ≤ C * (1 / sqrtScale n) := by
    filter_upwards [hb] with n hn
    simpa only [sqrtEquation_saddle (doubleSaddleScale_pos hd h₁ h₂ hz), c,
      sub_zero, div_eq_mul_inv, one_div, one_mul] using
      hn (c : ℂ) (by simpa only [Analytic.saddleDisk, rho_three, mul_one] using
        mem_closedBall_self (show 0 ≤ c / 4 by positivity))
  obtain ⟨r, hr, hrG, K, hK, hzeros⟩ := Analytic.exists_simple_zero_with_rate
    (ε := fun n => 1 / sqrtScale n) isOpen_ball ha
    (eventually_differentiableOn_exactSqrtEquation h₁ h₂ hz hc d .three)
    (differentiableOn_sqrtEquation_disk hc) hlim.tendstoLocallyUniformlyOn
    (sqrtEquation_saddle hc) (sqrtEquation_saddle_simple hc) hC hcenter
  exact ⟨r, hr, hrG, K, hK, by simpa only [mul_one_div] using hzeros⟩

/-- A stationary point of the actual kernel, with bounded unscaled displacement. -/
theorem exists_exact_sqrt_kernel_saddle {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∃ s ∈ Analytic.saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
        (sqrtScale n : ℂ) * s ∈ Analytic.kernelDomain A₁ A₂ n ∧
        deriv (kernel m d A₁ A₂ z .three n) ((sqrtScale n : ℂ) * s) = 0 ∧
        deriv (exactSqrtEquation d A₁ A₂ z .three n) s ≠ 0 ∧
        ‖(sqrtScale n : ℂ) * s - (sqrtScale n : ℂ) *
          (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ C := by
  obtain ⟨r, _, hrD, C, hC, hb⟩ := exists_exact_sqrt_saddle hd h₁ h₂ hz
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_sqrtDisk_mapsTo_kernelDomain h₁ h₂
    (doubleSaddleScale_pos hd h₁ h₂ hz)] with n hn hdom
  obtain ⟨s, hs, hzero, hsimple, hdist, _⟩ := hn
  have hσ : s ∈ Analytic.saddleDisk (doubleSaddleScale d A₁ A₂ z) .three := by
    simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall (hrD hs)
  refine ⟨s, hσ, hdom.2 hσ,
    (kernelLogDerivative_eq_zero_iff hz m d .three n (hdom.2 hσ)).mp hzero, hsimple, ?_⟩
  rw [← mul_sub, norm_mul, Complex.norm_of_nonneg (sqrtScale_pos hdom.1).le]
  exact (mul_le_mul_of_nonneg_left hdist (sqrtScale_pos hdom.1).le).trans_eq
    (mul_div_cancel₀ C (sqrtScale_pos hdom.1).ne')

end ThisWork.Trajectory
