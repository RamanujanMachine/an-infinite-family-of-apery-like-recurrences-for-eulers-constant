module

public import ThisWork.HigherRank.UniformTailDerivative
public import ThisWork.UniformTailDecay

/-! Uniform relative decay of the actual arbitrary-rank kernel along the
infinite horizontal tails, retaining the superexponential `t log t` bound. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem scaled_left_mem_kernelDomain {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (n : ℕ) {R t y : ℝ} (hR : 0 < R) (ht : 0 < t) (hy : y ≠ 0) :
    (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) ∈ kernelDomain r A n := by
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by
    simpa [Complex.mul_im] using mul_ne_zero hR.ne' hy)), ?_⟩
  intro i
  simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith [hA i, mul_pos hR ht, Nat.cast_nonneg (α := ℝ) n]

theorem hasDerivAt_log_norm_kernel_left {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (j : ℤ) {n : ℕ} (hn : 0 < n)
    {t y : ℝ} (ht : 0 < t) (hy : y ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log ‖kernel r m A z j n
      ((largeScale r n : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I))‖)
      (-largeScale r n * (exactSaddleEquation r A z j n (-(t : ℂ) + (y : ℂ) * Complex.I)).re) t := by
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hγ : HasDerivAt (fun u : ℝ => (largeScale r n : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I))
      (-(largeScale r n : ℂ)) t := by
    convert ((((hasDerivAt_id t).ofReal_comp).neg.add_const ((y : ℂ) * Complex.I)).const_mul
      (largeScale r n : ℂ)) using 1
    · funext u
      simp only [Pi.neg_apply, id_eq]
    · simp only [Complex.ofReal_one, mul_neg, mul_one]
  have hx := scaled_left_mem_kernelDomain hA n hR ht hy
  have hd : DifferentiableOn ℂ (kernel r m A z j n) (kernelDomain r A n) :=
    fun _ hs => (differentiableAt_kernel m z j n hs).differentiableWithinAt
  have h := Analytic.hasDerivAt_log_norm_comp (isOpen_kernelDomain r A n) hd
    (fun _ hs => kernel_ne_zero m z j n hs) hγ hx
  rw [← exactSaddleEquation_eq_logDeriv m z j n hx] at h
  simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, neg_mul] using h

theorem uniform_log_norm_kernel_tail_difference {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η H : ℝ} (hη : 0 < η)
    (m : ℕ) (z : ℝ) (j : ℤ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ -
        Real.log ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        -largeScale r n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)) := by
  obtain ⟨C, hC, hb⟩ := uniform_re_exactSaddleEquation_left_lower (H := H) hr hA hη z j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 a ha t hat y hy hyH
  have hy0 : y ≠ 0 := by intro he; rw [he, abs_zero] at hy; linarith
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  exact Analytic.log_decay_of_derivative_bound
    (df := fun u => -largeScale r n * (exactSaddleEquation r A z j n (-(u : ℂ) + (y : ℂ) * Complex.I)).re)
    (fun u hu => hasDerivAt_log_norm_kernel_left hA m z j hn0 (by linarith) hy0)
    (fun u hu => mul_le_mul_of_nonpos_left (hn u hu y hy hyH) (neg_nonpos.mpr hR.le)) ha hat

theorem uniform_kernel_tail_relative_decay {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η H : ℝ} (hη : 0 < η)
    (m : ℕ) (z : ℝ) (j : ℤ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 1 ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-largeScale r n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a))) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_tail_difference (H := H) hr hA hη m z j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 a ha t hat y hy hyH
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hKa : 0 < ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ :=
    norm_pos_iff.mpr (kernel_ne_zero m z j n (scaled_left_mem_kernelDomain hA n hR
      (by linarith) (by intro he; rw [he, abs_zero] at hy; linarith)))
  calc
    _ ≤ Real.exp (Real.log ‖kernel r m A z j n
        ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel r m A z j n
        ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ +
          (-largeScale r n * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)))) :=
      Real.exp_le_exp.mpr (by linarith [hn a ha t hat y hy hyH])
    _ = _ := by rw [Real.exp_add, Real.exp_log hKa]

theorem uniform_kernel_tail_exponential_decay {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η H : ℝ} (hη : 0 < η)
    (m : ℕ) (z : ℝ) (j : ℤ) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-q * largeScale r n * (t - a)) := by
  obtain ⟨C, _, hb⟩ := uniform_kernel_tail_relative_decay (H := H) hr hA hη m z j
  refine ⟨Real.exp (C + q + 1) + 1, by linarith [Real.exp_pos (C + q + 1)], ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 a ha t hat y hy hyH
  have ha1 : 1 ≤ a := by linarith [Real.exp_pos (C + q + 1)]
  have hapos : 0 < a := by linarith
  have hloga : C + q + 1 ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (C + q + 1))
      (by linarith : Real.exp (C + q + 1) ≤ a)
  have hlogt : Real.log a ≤ Real.log t := Real.log_le_log hapos hat
  have hphase : q * (t - a) ≤ t * Real.log t - a * Real.log a - (C + 1) * (t - a) := by
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (sub_nonneg.mpr hlogt),
      mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hloga)]
  have hR : 0 ≤ largeScale r n := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _).le
  exact (hn a ha1 t hat y hy hyH).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hphase hR])) (norm_nonneg _))

end ThisWork.HigherRank
