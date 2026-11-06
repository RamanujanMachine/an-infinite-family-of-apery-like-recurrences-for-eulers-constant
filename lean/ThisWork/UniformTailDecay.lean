module

public import ThisWork.UniformTailDerivative

/-! Integration of the uniform tail derivative estimate for the actual kernel. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem scaled_left_mem_kernelDomain {α₁ α₂ R t y : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (n : ℕ) (hR : 0 < R) (ht : 0 < t) (hy : y ≠ 0) :
    (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) ∈ kernelDomain α₁ α₂ n := by
  constructor
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa [Complex.mul_im] using mul_ne_zero hR.ne' hy
  · change ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)).re < _
    simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact lt_min (by nlinarith [mul_pos hR ht, mul_nonneg h₁.le (Nat.cast_nonneg (α := ℝ) n)])
      (by nlinarith [mul_pos hR ht, mul_nonneg h₂.le (Nat.cast_nonneg (α := ℝ) n)])

theorem hasDerivAt_log_norm_kernel_left {α₁ α₂ R t y : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n : ℕ)
    (hR : 0 < R) (ht : 0 < t) (hy : y ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log ‖kernel α₁ α₂ j n
      ((R : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I))‖)
      (-R * (kernelLogDerivative α₁ α₂ j n
        ((R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))).re) t := by
  have hγ : HasDerivAt (fun u : ℝ => (R : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I)) (-(R : ℂ)) t := by
    convert ((((hasDerivAt_id t).ofReal_comp).neg.add_const ((y : ℂ) * Complex.I)).const_mul (R : ℂ)) using 1
    · funext u
      simp only [Pi.neg_apply, id_eq]
    · simp only [Complex.ofReal_one, mul_neg, mul_one]
  have hx := scaled_left_mem_kernelDomain h₁ h₂ n hR ht hy
  simpa only [logDeriv_kernel j n hx, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, neg_mul] using
    hasDerivAt_log_norm_comp (isOpen_kernelDomain α₁ α₂ n) (differentiableOn_kernel α₁ α₂ j n)
      (fun z hz => kernel_ne_zero j n hz) hγ hx

theorem log_decay_of_derivative_bound {f df : ℝ → ℝ} {R C a t : ℝ}
    (hf : ∀ u : ℝ, 1 ≤ u → HasDerivAt f (df u) u)
    (hb : ∀ u : ℝ, 1 ≤ u → df u ≤ -R * (Real.log u - C))
    (ha : 1 ≤ a) (hat : a ≤ t) :
    f t - f a ≤ -R * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)) := by
  have hd (u : ℝ) (hu : 1 ≤ u) :
      HasDerivAt (fun v : ℝ => f v + R * (v * Real.log v - (C + 1) * v))
        (df u + R * (Real.log u - C)) u := by
    convert (hf u hu).add ((((hasDerivAt_id u).mul (Real.hasDerivAt_log (by linarith : u ≠ 0))).sub
      ((hasDerivAt_id u).const_mul (C + 1))).const_mul R) using 1
    · funext v
      rfl
    · simp only [id_eq, one_mul, mul_one, mul_inv_cancel₀ (show u ≠ 0 by linarith)]
      ring
  have hm : AntitoneOn (fun v : ℝ => f v + R * (v * Real.log v - (C + 1) * v)) (Ici 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
      (fun u hu => by linarith [hb u (interior_subset hu)])
  nlinarith [hm ha (ha.trans hat) hat]

/-- A uniform integrated estimate retaining the superexponential `t log t`
decay and comparing two points on the same actual horizontal tail. -/
theorem uniform_log_norm_kernel_tail_difference {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ -
        Real.log ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        -largeScale n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)) := by
  obtain ⟨C, hC, hb⟩ := uniform_re_exactSaddleEquation_left_lower (H := H) h₁ h₂ hη j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ a ha t hat y hy hyH
  have hy₀ : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; linarith
  exact log_decay_of_derivative_bound
    (df := fun u => -largeScale n * (exactSaddleEquation α₁ α₂ j n (-(u : ℂ) + (y : ℂ) * Complex.I)).re)
    (fun u hu => hasDerivAt_log_norm_kernel_left h₁ h₂ j n (largeScale_pos hn₀) (by linarith) hy₀)
    (fun u hu => mul_le_mul_of_nonpos_left (hn u hu y hy hyH) (neg_nonpos.mpr (largeScale_pos hn₀).le))
    ha hat

theorem uniform_kernel_tail_relative_decay {α₁ α₂ η H : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-largeScale n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a))) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_tail_difference (H := H) h₁ h₂ hη j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ a ha t hat y hy hyH
  have hKa : 0 < ‖kernel α₁ α₂ j n
      ((largeScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ :=
    norm_pos_iff.mpr (kernel_ne_zero j n (scaled_left_mem_kernelDomain h₁ h₂ n (largeScale_pos hn₀)
      (by linarith) (by intro h; rw [h, abs_zero] at hy; linarith)))
  calc
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n
        ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel α₁ α₂ j n
        ((largeScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ +
          (-largeScale n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)))) :=
      Real.exp_le_exp.mpr (by linarith [hn a ha t hat y hy hyH])
    _ = _ := by rw [Real.exp_add, Real.exp_log hKa]

end ThisWork
