module
public import ThisWork.Trajectory.ReflectedEquation
public import ThisWork.SaddleStability
/-! Exact simple growing saddles of the reflected kernel. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

theorem differentiableAt_digamma_re_pos {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.digamma w := by
  let U : Set ℂ := {v | 0 < v.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : DifferentiableOn ℂ Complex.Gamma U := fun v hv =>
    (Complex.differentiableAt_Gamma v (not_neg_nat_of_mem_slitPlane
      (Complex.mem_slitPlane_iff.mpr (Or.inl hv)))).differentiableWithinAt
  have hq := (hΓ.deriv hU).div hΓ (fun v hv => Complex.Gamma_ne_zero_of_re_pos hv)
  have he : (fun v => deriv Complex.Gamma v / Complex.Gamma v) = Complex.digamma := by
    funext v
    rw [Complex.digamma_def, logDeriv_apply]
  change DifferentiableOn ℂ (fun v => deriv Complex.Gamma v / Complex.Gamma v) U at hq
  rw [he] at hq
  exact hq.differentiableAt (hU.mem_nhds hw)

theorem eventually_differentiableOn_reflectedEquation {d : ℕ} {A₁ A₂ z c : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (reflectedEquation d A₁ A₂ z n)
      (ball (c : ℂ) (c / 4)) := by
  filter_upwards [eventually_right_factor_conditions (Nat.cast_pos.mpr hd) (5 * c / 4),
    eventually_gt_atTop (0 : ℕ)] with n hD hn
  intro s hs
  have hsD : s ∈ saddleDisk c .three := by
    simpa only [saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs
  have hre : 0 < s.re := by
    have h := saddleDisk_region hc .three hsD
    change c / 2 ≤ s.re at h
    linarith
  have hR := sqrtScale_pos hn
  have hsr : ((sqrtScale n : ℂ) * s).re = sqrtScale n * s.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hbound := mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans (saddleDisk_norm_le hc .three hsD)) hR.le
  have hdR : 0 < ((d : ℂ) * n - (sqrtScale n : ℂ) * s).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith [hD.1, hD.2]
  have hAR (A : ℝ) (hA : 0 < A) : 0 < ((A : ℂ) * n + (sqrtScale n : ℂ) * s + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.one_re, zero_mul, mul_zero, sub_zero]
    positivity
  have h1R : 0 < (1 + (sqrtScale n : ℂ) * s).re := by
    rw [Complex.add_re, Complex.one_re, hsr]
    positivity
  have hDψ := (differentiableAt_digamma_re_pos hdR).comp s
    (differentiableAt_const _ |>.sub ((differentiableAt_id).const_mul (sqrtScale n : ℂ)))
  have hAψ (A : ℝ) (hA : 0 < A) := (differentiableAt_digamma_re_pos (hAR A hA)).comp s
    ((((differentiableAt_id).const_mul (sqrtScale n : ℂ)).const_add ((A : ℂ) * n)).add_const 1)
  have h1ψ := (differentiableAt_digamma_re_pos h1R).comp s
    (((differentiableAt_id).const_mul (sqrtScale n : ℂ)).const_add 1)
  exact ((((hDψ.neg.add (hAψ A₁ h₁)).add (hAψ A₂ h₂)).sub (h1ψ.const_mul 2)).add_const
    (Real.log z : ℂ)).differentiableWithinAt

theorem uniform_reflectedEquation_disk {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖reflectedEquation d A₁ A₂ z n s - (-sqrtEquation (doubleSaddleScale d A₁ A₂ z) s)‖ ≤
        C / sqrtScale n := by
  have hc := doubleSaddleScale_pos hd h₁ h₂ hz
  simpa only [sub_neg_eq_add] using uniform_reflectedEquation_right hd h₁ h₂ hz
    (η := doubleSaddleScale d A₁ A₂ z / 2) (by positivity)
    (M := 5 * doubleSaddleScale d A₁ A₂ z / 4) (by positivity)
    (fun s hs => saddleDisk_norm_le hc .three hs) (fun s hs => saddleDisk_region hc .three hs)

theorem reflectedEquation_tendsto_uniform_disk {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    TendstoUniformlyOn (fun n => reflectedEquation d A₁ A₂ z n)
      (fun s => -sqrtEquation (doubleSaddleScale d A₁ A₂ z) s) atTop
      (Analytic.saddleDisk (doubleSaddleScale d A₁ A₂ z) .three) := by
  obtain ⟨C, _, hb⟩ := uniform_reflectedEquation_disk hd h₁ h₂ hz
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : Tendsto (fun n => C / sqrtScale n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp sqrtScale_tendsto).const_mul C
  filter_upwards [hb, he.eventually (gt_mem_nhds hε)] with n hn hεn s hs
  rw [dist_eq_norm, norm_sub_rev]
  exact (hn s hs).trans_lt hεn


theorem exists_exact_reflected_saddle {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ r > 0, ball (doubleSaddleScale d A₁ A₂ z : ℂ) r ⊆
      ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) ∧
      ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
        ∃ s ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) r,
          reflectedEquation d A₁ A₂ z n s = 0 ∧
          deriv (reflectedEquation d A₁ A₂ z n) s ≠ 0 ∧
          ‖s - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ C / sqrtScale n ∧
          ∀ t ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) r,
            reflectedEquation d A₁ A₂ z n t = 0 → t = s := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  have ha : (c : ℂ) ∈ ball (c : ℂ) (c / 4) := mem_ball_self (by positivity)
  obtain ⟨C, hC, hb⟩ := uniform_reflectedEquation_disk hd h₁ h₂ hz
  have hlim : TendstoUniformlyOn (fun n => reflectedEquation d A₁ A₂ z n)
      (fun s => -sqrtEquation c s) atTop (ball (c : ℂ) (c / 4)) :=
    (reflectedEquation_tendsto_uniform_disk hd h₁ h₂ hz).mono fun s hs => by
      simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs
  have hcenter : ∀ᶠ n : ℕ in atTop,
      ‖reflectedEquation d A₁ A₂ z n (c : ℂ)‖ ≤ C * (1 / sqrtScale n) := by
    filter_upwards [hb] with n hn
    simpa only [sqrtEquation_saddle (doubleSaddleScale_pos hd h₁ h₂ hz), neg_zero, c,
      sub_zero, div_eq_mul_inv, one_div, one_mul] using
      hn (c : ℂ) (by simpa only [Analytic.saddleDisk, rho_three, mul_one] using
        mem_closedBall_self (show 0 ≤ c / 4 by positivity))
  obtain ⟨r, hr, hrG, K, hK, hzeros⟩ := Analytic.exists_simple_zero_with_rate
    (ε := fun n => 1 / sqrtScale n) isOpen_ball ha
    (eventually_differentiableOn_reflectedEquation hd h₁ h₂ hc)
    (differentiableOn_sqrtEquation_disk hc).neg hlim.tendstoLocallyUniformlyOn
    (by simp only [Pi.neg_apply, sqrtEquation_saddle hc, neg_zero]) (by simpa only [deriv.neg, neg_ne_zero] using sqrtEquation_saddle_simple hc) hC hcenter
  exact ⟨r, hr, hrG, K, hK, by simpa only [mul_one_div] using hzeros⟩


end ThisWork.Trajectory
