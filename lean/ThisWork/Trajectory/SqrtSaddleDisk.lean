module

public import ThisWork.Trajectory.SqrtApproximation
public import ThisWork.Trajectory.KernelSaddle
public import ThisWork.SaddleDisks

/-! Uniform equation estimates and holomorphy near the positive square-root saddle. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

/-- The fixed disk stays inside the actual Gamma kernel domain for large indices. -/
theorem eventually_sqrtDisk_mapsTo_kernelDomain {A₁ A₂ c : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ MapsTo (fun s : ℂ => (sqrtScale n : ℂ) * s)
      (Analytic.saddleDisk c .three) (Analytic.kernelDomain A₁ A₂ n) := by
  let M := 5 * c / 4
  filter_upwards [eventually_right_factor_conditions h₁ M,
    eventually_right_factor_conditions h₂ M, eventually_gt_atTop (0 : ℕ)] with n hn₁ hn₂ hn
  refine ⟨hn, fun s hs => ?_⟩
  have hR := sqrtScale_pos hn
  have hslit := Analytic.saddleDisk_mem_slitPlane hc .three hs
  have hnorm : ‖s‖ ≤ M := Analytic.saddleDisk_norm_le hc .three hs
  have hre : ((sqrtScale n : ℂ) * s).re ≤ sqrtScale n * M := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans hnorm) hR.le
  refine ⟨?_, ?_⟩
  · apply (div_pos_real_mem_slitPlane_iff hR _).mp
    simpa only [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')] using hslit
  · change ((sqrtScale n : ℂ) * s).re < min (A₁ * n + 1) (A₂ * n + 1)
    exact lt_min (by linarith [hn₁.1, hn₁.2]) (by linarith [hn₂.1, hn₂.2])

theorem uniform_exactSqrtEquation_disk {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Analytic.saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
        ‖exactSqrtEquation d A₁ A₂ z .three n s -
          sqrtEquation (doubleSaddleScale d A₁ A₂ z) s‖ ≤ C / sqrtScale n := by
  have hc := doubleSaddleScale_pos hd h₁ h₂ hz
  simpa only [limitingSqrtEquation, twist_three, add_zero] using
    uniform_exactSqrtEquation_right hd h₁ h₂ hz (η := doubleSaddleScale d A₁ A₂ z / 2)
      (by positivity) .three (M := 5 * doubleSaddleScale d A₁ A₂ z / 4) (by positivity)
      (fun s hs => Analytic.saddleDisk_norm_le hc .three hs)
      (fun s hs => Analytic.saddleDisk_region hc .three hs)

theorem eventually_differentiableOn_exactSqrtEquation {A₁ A₂ z c : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hc : 0 < c) (d : ℕ) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (exactSqrtEquation d A₁ A₂ z j n)
      (ball (c : ℂ) (c / 4)) := by
  filter_upwards [eventually_sqrtDisk_mapsTo_kernelDomain h₁ h₂ hc] with n hn
  change DifferentiableOn ℂ (fun s => kernelLogDerivative d A₁ A₂ z j n ((sqrtScale n : ℂ) * s)) _
  exact (differentiableOn_kernelLogDerivative hz d A₁ A₂ j n).comp
    (differentiableOn_id.const_mul (sqrtScale n : ℂ))
    (fun s hs => hn.2 (by
      simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs))

theorem exactSqrtEquation_tendsto_uniform_disk {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    TendstoUniformlyOn (fun n => exactSqrtEquation d A₁ A₂ z .three n)
      (sqrtEquation (doubleSaddleScale d A₁ A₂ z)) atTop
      (Analytic.saddleDisk (doubleSaddleScale d A₁ A₂ z) .three) := by
  obtain ⟨C, _, hb⟩ := uniform_exactSqrtEquation_disk hd h₁ h₂ hz
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : Tendsto (fun n => C / sqrtScale n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp sqrtScale_tendsto).const_mul C
  filter_upwards [hb, he.eventually (gt_mem_nhds hε)] with n hn hεn s hs
  rw [dist_eq_norm, norm_sub_rev]
  exact (hn s hs).trans_lt hεn

theorem differentiableOn_sqrtEquation_disk {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (sqrtEquation c) (ball (c : ℂ) (c / 4)) := by
  intro s hs
  exact (hasDerivAt_sqrtEquation hc ((div_pos_real_mem_slitPlane_iff hc s).mpr
    (Analytic.saddleDisk_mem_slitPlane hc .three (by
      simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs)))).differentiableAt.differentiableWithinAt

end ThisWork.Trajectory
