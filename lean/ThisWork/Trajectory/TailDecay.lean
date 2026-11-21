module

public import ThisWork.Trajectory.TailDerivative
public import ThisWork.UniformTailDecay

/-! Uniform integrated tail decay for the actual unequal-slope kernels. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

theorem hasDerivAt_log_norm_kernel_left {A₁ A₂ z R t y : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m d : ℕ) (j : Branch) (n : ℕ)
    (hR : 0 < R) (ht : 0 < t) (hy : y ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log ‖kernel m d A₁ A₂ z j n
      ((R : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I))‖)
      (-R * (kernelLogDerivative d A₁ A₂ z j n
        ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))).re) t := by
  have hγ : HasDerivAt (fun u : ℝ => (R : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I)) (-(R : ℂ)) t := by
    convert ((((hasDerivAt_id t).ofReal_comp).neg.add_const ((y : ℂ) * Complex.I)).const_mul (R : ℂ)) using 1
    · funext u
      simp only [Pi.neg_apply, id_eq]
    · simp only [Complex.ofReal_one, mul_neg, mul_one]
  have hx := Analytic.scaled_left_mem_kernelDomain h₁ h₂ n hR ht hy
  simpa only [logDeriv_kernel hz m d j n hx, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, neg_mul] using
    Analytic.hasDerivAt_log_norm_comp (Analytic.isOpen_kernelDomain A₁ A₂ n)
      (differentiableOn_kernel hz m d A₁ A₂ j n)
      (fun w hw => kernel_ne_zero hz m d j n hw) hγ hx

/-- The superexponential tail comparison is uniform even across the moving pole family. -/
theorem uniform_log_norm_kernel_tail_difference {d : ℕ} {A₁ A₂ z η H : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) (m : ℕ) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ -
        Real.log ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        -sqrtScale n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)) := by
  obtain ⟨C, hC, hb⟩ := uniform_re_exactSqrtEquation_left_lower (z := z) (H := H) hd h₁ h₂ hη j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ a ha t hat y hy hyH
  have hy₀ : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; linarith
  exact Analytic.log_decay_of_derivative_bound
    (df := fun u => -sqrtScale n * (exactSqrtEquation d A₁ A₂ z j n (-(u : ℂ) + (y : ℂ) * Complex.I)).re)
    (fun u hu => hasDerivAt_log_norm_kernel_left h₁ h₂ hz m d j n (sqrtScale_pos hn₀) (by linarith) hy₀)
    (fun u hu => mul_le_mul_of_nonpos_left (hn u hu y hy hyH) (neg_nonpos.mpr (sqrtScale_pos hn₀).le))
    ha hat

theorem uniform_kernel_tail_relative_decay {d : ℕ} {A₁ A₂ z η H : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) (m : ℕ) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-sqrtScale n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a))) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_tail_difference (H := H) hd h₁ h₂ hz hη m j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ a ha t hat y hy hyH
  have hKa : 0 < ‖kernel m d A₁ A₂ z j n
      ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ :=
    norm_pos_iff.mpr (kernel_ne_zero hz m d j n (Analytic.scaled_left_mem_kernelDomain h₁ h₂ n
      (sqrtScale_pos hn₀) (by linarith) (by intro h; rw [h, abs_zero] at hy; linarith)))
  calc
    _ ≤ Real.exp (Real.log ‖kernel m d A₁ A₂ z j n
        ((sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel m d A₁ A₂ z j n
        ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ +
          (-sqrtScale n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)))) :=
      Real.exp_le_exp.mpr (by linarith [hn a ha t hat y hy hyH])
    _ = _ := by rw [Real.exp_add, Real.exp_log hKa]

/-- Beyond a fixed anchor, every prescribed exponential rate is available uniformly in `n`. -/
theorem uniform_kernel_tail_exponential_decay {d : ℕ} {A₁ A₂ z η H : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) (m : ℕ) (j : Branch) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-q * sqrtScale n * (t - a)) := by
  obtain ⟨C, _, hb⟩ := uniform_kernel_tail_relative_decay (H := H) hd h₁ h₂ hz hη m j
  refine ⟨Real.exp (C + q + 1) + 1, by linarith [Real.exp_pos (C + q + 1)], ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ a ha t hat y hy hyH
  have ha₁ : 1 ≤ a := by linarith [Real.exp_pos (C + q + 1)]
  have hlog : C + q + 1 ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (C + q + 1))
      (show Real.exp (C + q + 1) ≤ a by linarith)
  have hexp : q * (t - a) ≤ t * Real.log t - a * Real.log a - (C + 1) * (t - a) := by
    have hlogt := Real.log_le_log (show 0 < a by linarith) hat
    nlinarith [mul_le_mul_of_nonneg_left hlogt (show 0 ≤ t by linarith),
      mul_le_mul_of_nonneg_right hlog (sub_nonneg.mpr hat)]
  exact (hn a ha₁ t hat y hy hyH).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by nlinarith [mul_le_mul_of_nonneg_left hexp (sqrtScale_pos hn₀).le])) (norm_nonneg _))

end ThisWork.Trajectory
