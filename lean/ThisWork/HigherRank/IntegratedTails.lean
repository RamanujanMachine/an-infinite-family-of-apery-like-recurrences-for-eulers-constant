module

public import ThisWork.HigherRank.UniformTailDecay
public import ThisWork.IntegratedTails

/-! Uniform integral bounds for arbitrary-rank power-moment tails, relative
to the actual kernel value at the finite endpoint. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem integral_norm_le_shifted_exp_tail {f : ℝ → ℂ} {C a T : ℝ} (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi T)))
    (hb : ∀ t ∈ Ioi T, ‖f t‖ ≤ C * Real.exp (-a * (t - T))) :
    IntegrableOn f (Ioi T) ∧ ‖∫ t in Ioi T, f t‖ ≤ C / a := by
  have h := Analytic.integral_norm_le_exp_tail ha hf
    (C := C * Real.exp (a * T)) (fun t ht => by
      convert hb t ht using 1
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [mul_assoc, ← Real.exp_add, show a * T + -a * T = 0 by ring, Real.exp_zero, mul_one]

noncomputable def scaledLeftMomentKernel (r b : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n k : ℕ) (y t : ℝ) : ℂ :=
  (-(t : ℂ) + (y : ℂ) * Complex.I) ^ k *
    kernel r b A z j n ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))

theorem uniform_integrated_moment_tail_from_endpoint {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η H : ℝ} (hη : 0 < η) (hH : 0 ≤ H)
    (b : ℕ) (z : ℝ) (j : ℤ) (k : ℕ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      IntegrableOn (scaledLeftMomentKernel r b A z j n k y) (Ioi T) ∧
        ‖∫ t in Ioi T, scaledLeftMomentKernel r b A z j n k y t‖ ≤
          Real.exp T * ‖kernel r b A z j n
            ((largeScale r n : ℂ) * (-(T : ℂ) + (y : ℂ) * Complex.I))‖ / largeScale r n := by
  obtain ⟨T₀, hT₀, hb⟩ := uniform_kernel_tail_exponential_decay (H := H) hr hA hη b z j 2
  obtain ⟨Tp, hTp⟩ := eventually_atTop.mp
    (Analytic.eventually_shifted_pow_le_exp (D := H + 1) (by positivity) k)
  let T := max T₀ Tp
  have hT : 1 ≤ T := hT₀.trans (le_max_left _ _)
  refine ⟨T, hT, ?_⟩
  filter_upwards [hb, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (1 : ℝ))] with n hn hR y hy hyH
  have hR0 : 0 < largeScale r n := zero_lt_one.trans_le hR
  have hy0 : y ≠ 0 := by intro he; rw [he, abs_zero] at hy; linarith
  have hcont : ContinuousOn (scaledLeftMomentKernel r b A z j n k y) (Ioi T) := by
    have hk : ContinuousOn (fun t : ℝ => kernel r b A z j n
        ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))) (Ioi T) :=
      (show ContinuousOn (kernel r b A z j n) (kernelDomain r A n) from
        (show DifferentiableOn ℂ (kernel r b A z j n) (kernelDomain r A n) from
          fun _ hs => (differentiableAt_kernel b z j n hs).differentiableWithinAt).continuousOn).comp
        (by fun_prop) (fun t ht => scaled_left_mem_kernelDomain hA n hR0
          (by linarith [show T < t from ht]) hy0)
    exact (by fun_prop : ContinuousOn (fun t : ℝ => (-(t : ℂ) + (y : ℂ) * Complex.I) ^ k) (Ioi T)).mul hk
  apply integral_norm_le_shifted_exp_tail hR0 (hcont.aestronglyMeasurable measurableSet_Ioi)
  intro t ht
  have htT : T ≤ t := ht.le
  have ht0 : 0 ≤ t := by linarith
  have hpoly : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ^ k ≤ Real.exp t := by
    have hs : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ t + H := by
      simpa only [Nat.cast_zero, zero_sub, norm_neg, zero_add] using Analytic.norm_polynomial_left_le ht0 hyH 0
    exact (pow_le_pow_left₀ (norm_nonneg _) (hs.trans (by linarith : t + H ≤ t + (H + 1))) k).trans
      (hTp t ((le_max_right T₀ Tp).trans htT))
  have hkernel := hn T (le_max_left _ _) t htT y hy hyH
  rw [scaledLeftMomentKernel, norm_mul, norm_pow]
  calc
    _ ≤ Real.exp t * (‖kernel r b A z j n
        ((largeScale r n : ℂ) * (-(T : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-2 * largeScale r n * (t - T))) :=
      mul_le_mul hpoly hkernel (norm_nonneg _) (Real.exp_pos t).le
    _ = ‖kernel r b A z j n ((largeScale r n : ℂ) * (-(T : ℂ) + (y : ℂ) * Complex.I))‖ *
        Real.exp (t + (-2 * largeScale r n * (t - T))) := by rw [Real.exp_add]; ring
    _ ≤ ‖kernel r b A z j n ((largeScale r n : ℂ) * (-(T : ℂ) + (y : ℂ) * Complex.I))‖ *
        Real.exp (T - largeScale r n * (t - T)) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr htT)])) (norm_nonneg _)
    _ = _ := by
      rw [show T - largeScale r n * (t - T) = T + (-largeScale r n * (t - T)) by ring, Real.exp_add]
      ring

end ThisWork.HigherRank
