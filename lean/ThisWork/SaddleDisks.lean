module

public import ThisWork.SaddleApproximation

/-! Fixed saddle disks and the uniform exact-equation approximation on them. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

noncomputable def saddleDisk (c : ℝ) (j : Branch) : Set ℂ :=
  closedBall ((c : ℂ) * rho j) (c / 4)

def saddleRegion (c : ℝ) (j : Branch) (s : ℂ) : Prop :=
  match j with
  | .one | .two => s.re ≤ -(c / 4) ∧ c / 4 ≤ |s.im|
  | .three => c / 2 ≤ s.re

theorem saddleDisk_norm_le {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ} (hs : s ∈ saddleDisk c j) :
    ‖s‖ ≤ 5 * c / 4 := by
  have hd : ‖s - (c : ℂ) * rho j‖ ≤ c / 4 := by
    simpa only [saddleDisk, mem_closedBall, dist_eq_norm] using hs
  have hz : ‖(c : ℂ) * rho j‖ = c := by rw [norm_mul, norm_rho, mul_one, Complex.norm_of_nonneg hc.le]
  have h := norm_add_le (s - (c : ℂ) * rho j) ((c : ℂ) * rho j)
  rw [sub_add_cancel, hz] at h
  linarith

theorem saddleDisk_region {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ} (hs : s ∈ saddleDisk c j) :
    saddleRegion c j s := by
  have hd : ‖s - (c : ℂ) * rho j‖ ≤ c / 4 := by
    simpa only [saddleDisk, mem_closedBall, dist_eq_norm] using hs
  have hRe : |s.re - ((c : ℂ) * rho j).re| ≤ c / 4 := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (s - (c : ℂ) * rho j)).trans hd
  have hIm : |s.im - ((c : ℂ) * rho j).im| ≤ c / 4 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (s - (c : ℂ) * rho j)).trans hd
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num)
  have hm := mul_le_mul_of_nonneg_right hsqrt hc.le
  cases j
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, rho_one_re, rho_one_im] at hRe hIm
    obtain ⟨hr₀, hr₁⟩ := abs_le.mp hRe
    obtain ⟨hi₀, hi₁⟩ := abs_le.mp hIm
    constructor
    · nlinarith
    · nlinarith [neg_le_abs s.im]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, rho_two_re, rho_two_im] at hRe hIm
    obtain ⟨hr₀, hr₁⟩ := abs_le.mp hRe
    obtain ⟨hi₀, hi₁⟩ := abs_le.mp hIm
    constructor
    · nlinarith
    · nlinarith [le_abs_self s.im]
  · simp only [rho_three, mul_one, Complex.ofReal_re] at hRe
    obtain ⟨hr₀, hr₁⟩ := abs_le.mp hRe
    change c / 2 ≤ s.re
    linarith

/-- The uniform saddle-equation estimate in Step 1 of Appendix A, proved for
the actual Gamma-product integrands on explicit disks around all three roots. -/
theorem uniform_exactSaddleEquation_disk {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤ C * smallParameter n := by
  let c := saddleScale α₁ α₂
  have hc : 0 < c := saddleScale_pos h₁ h₂
  cases j
  · apply uniform_exactSaddleEquation_left h₁ h₂ (κ := c / 4) (η := c / 4)
      (by positivity) (by positivity) .one (M := 5 * c / 4) (by positivity)
    · exact fun s hs => saddleDisk_norm_le hc .one hs
    · exact fun s hs => saddleDisk_region hc .one hs
  · apply uniform_exactSaddleEquation_left h₁ h₂ (κ := c / 4) (η := c / 4)
      (by positivity) (by positivity) .two (M := 5 * c / 4) (by positivity)
    · exact fun s hs => saddleDisk_norm_le hc .two hs
    · exact fun s hs => saddleDisk_region hc .two hs
  · apply uniform_exactSaddleEquation_right h₁ h₂ (κ := c / 2)
      (by positivity) .three (M := 5 * c / 4) (by positivity)
    · exact fun s hs => saddleDisk_norm_le hc .three hs
    · exact fun s hs => saddleDisk_region hc .three hs

theorem saddleDisk_mem_slitPlane {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ} (hs : s ∈ saddleDisk c j) :
    s ∈ Complex.slitPlane := by
  have h := saddleDisk_region hc j hs
  apply Complex.mem_slitPlane_iff.mpr
  cases j
  · right
    intro he
    change s.re ≤ -(c / 4) ∧ c / 4 ≤ |s.im| at h
    rw [he, abs_zero] at h
    linarith [h.2]
  · right
    intro he
    change s.re ≤ -(c / 4) ∧ c / 4 ≤ |s.im| at h
    rw [he, abs_zero] at h
    linarith [h.2]
  · left
    change c / 2 ≤ s.re at h
    linarith

theorem eventually_saddleDisk_mapsTo_kernelDomain {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ MapsTo (fun s : ℂ => (largeScale n : ℂ) * s)
      (saddleDisk (saddleScale α₁ α₂) j) (kernelDomain α₁ α₂ n) := by
  let c := saddleScale α₁ α₂
  let M := 5 * c / 4
  have hc : 0 < c := saddleScale_pos h₁ h₂
  filter_upwards [eventually_right_factor_conditions h₁ M,
    eventually_right_factor_conditions h₂ M, eventually_gt_atTop (0 : ℕ)] with n hn₁ hn₂ hn
  refine ⟨hn, fun s hs => ?_⟩
  have hR := largeScale_pos hn
  have hslit := saddleDisk_mem_slitPlane hc j hs
  have hnorm : ‖s‖ ≤ M := saddleDisk_norm_le hc j hs
  have hre : ((largeScale n : ℂ) * s).re ≤ largeScale n * M := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans hnorm) hR.le
  refine ⟨?_, ?_⟩
  · apply (div_pos_real_mem_slitPlane_iff hR _).mp
    simpa only [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')] using hslit
  · change ((largeScale n : ℂ) * s).re < min (α₁ * n + 1) (α₂ * n + 1)
    exact lt_min (by linarith [hn₁.1, hn₁.2]) (by linarith [hn₂.1, hn₂.2])

theorem eventually_differentiableOn_exactSaddleEquation {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (exactSaddleEquation α₁ α₂ j n)
      (ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4)) := by
  filter_upwards [eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j] with n hn
  change DifferentiableOn ℂ (fun s => kernelLogDerivative α₁ α₂ j n ((largeScale n : ℂ) * s)) _
  exact (differentiableOn_kernelLogDerivative α₁ α₂ j n).comp
    (differentiableOn_id.const_mul (largeScale n : ℂ))
    (fun s hs => hn.2 (ball_subset_closedBall hs))

theorem exactSaddleEquation_tendsto_uniform_disk {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    TendstoUniformlyOn (fun n => exactSaddleEquation α₁ α₂ j n)
      (limitingEquation j (saddleScale α₁ α₂)) atTop (saddleDisk (saddleScale α₁ α₂) j) := by
  obtain ⟨C, hC, hb⟩ := uniform_exactSaddleEquation_disk h₁ h₂ j
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : Tendsto (fun n => C * smallParameter n) atTop (𝓝 0) := by
    simpa only [mul_zero] using smallParameter_tendsto.const_mul C
  filter_upwards [hb, he.eventually (gt_mem_nhds hε)] with n hn hεn s hs
  rw [dist_eq_norm, norm_sub_rev]
  exact (hn s hs).trans_lt hεn

theorem differentiableOn_limitingEquation_disk {c : ℝ} (hc : 0 < c) (j : Branch) :
    DifferentiableOn ℂ (limitingEquation j c) (ball ((c : ℂ) * rho j) (c / 4)) :=
  fun s hs => (hasDerivAt_limitingEquation j hc
    ((div_pos_real_mem_slitPlane_iff hc s).mpr
      (saddleDisk_mem_slitPlane hc j (ball_subset_closedBall hs)))).differentiableAt.differentiableWithinAt

end ThisWork
