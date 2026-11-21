module

public import ThisWork.Trajectory.TailDecay
public import ThisWork.IntegratedTails

/-! Uniform integrable majorants for the infinite trajectory-contour pieces. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric MeasureTheory
open scoped Topology

theorem integral_norm_le_shifted_exp_tail {f : ℝ → ℂ} {C a T : ℝ} (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi T)))
    (hb : ∀ t ∈ Ioi T, ‖f t‖ ≤ C * Real.exp (-a * (t - T))) :
    IntegrableOn f (Ioi T) ∧ ‖∫ t in Ioi T, f t‖ ≤ C / a := by
  have hb' : ∀ t ∈ Ioi T, ‖f t‖ ≤ (C * Real.exp (a * T)) * Real.exp (-a * t) := by
    intro t ht
    convert hb t ht using 1
    rw [show -a * (t - T) = a * T + -a * t by ring, Real.exp_add]
    ring
  obtain ⟨hi, hn⟩ := Analytic.integral_norm_le_exp_tail ha hf hb'
  refine ⟨hi, hn.trans_eq ?_⟩
  rw [mul_assoc, ← Real.exp_add, show a * T + -a * T = 0 by ring, Real.exp_zero, mul_one]

@[expose] noncomputable def leftMomentKernel (m d : ℕ) (A₁ A₂ z : ℝ) (j : Branch) (n k : ℕ)
    (y t : ℝ) : ℂ :=
  (-(t : ℂ) + (y : ℂ) * Complex.I) ^ k *
    kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))

theorem uniform_leftMomentKernel_tail_bound {d : ℕ} {A₁ A₂ z η H : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) (hH : 0 ≤ H) (m : ℕ) (j : Branch) (k : ℕ) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      ‖leftMomentKernel m d A₁ A₂ z j n k y t‖ ≤
        Real.exp a * ‖kernel m d A₁ A₂ z j n
          ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
            Real.exp (-q * sqrtScale n * (t - a)) := by
  obtain ⟨T, hT, hb⟩ := uniform_kernel_tail_exponential_decay (H := H) hd h₁ h₂ hz hη m j (q + 1)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (Analytic.eventually_shifted_pow_le_exp hH k)
  refine ⟨max T A, hT.trans (le_max_left _ _), ?_⟩
  filter_upwards [hb, sqrtScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hR a ha t hat y hy hyH
  have ht₁ : 1 ≤ t := hT.trans ((le_max_left _ _).trans (ha.trans hat))
  have hnorm : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ t + H := by
    simpa only [Nat.cast_zero, zero_sub, norm_neg, zero_add] using
      Analytic.norm_polynomial_left_le (show 0 ≤ t by linarith) hyH 0
  have hp : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ^ k ≤ Real.exp t :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm k).trans
      (hA t ((le_max_right _ _).trans (ha.trans hat)))
  have hK := hn a ((le_max_left _ _).trans ha) t hat y hy hyH
  let K := ‖kernel m d A₁ A₂ z j n
    ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖
  calc
    _ = ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ^ k *
        ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ := by
      simp only [leftMomentKernel, norm_mul, norm_pow]
    _ ≤ Real.exp t * (K * Real.exp (-(q + 1) * sqrtScale n * (t - a))) :=
      mul_le_mul hp hK (norm_nonneg _) (Real.exp_pos _).le
    _ = K * Real.exp (t + (-(q + 1) * sqrtScale n * (t - a))) := by rw [Real.exp_add]; ring
    _ ≤ K * Real.exp (a + (-q * sqrtScale n * (t - a))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hR (sub_nonneg.mpr hat)])) (norm_nonneg _)
    _ = _ := by rw [Real.exp_add]; ring

/-- Every fixed moment has a uniform integrable tail majorant, relative to its anchor. -/
theorem uniform_integrated_leftMoment_tail {d : ℕ} {A₁ A₂ z η H q : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) (hH : 0 ≤ H) (hq : 0 < q) (m : ℕ) (j : Branch) (k : ℕ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      IntegrableOn (leftMomentKernel m d A₁ A₂ z j n k y) (Ioi a) ∧
      ‖∫ t in Ioi a, leftMomentKernel m d A₁ A₂ z j n k y t‖ ≤
        Real.exp a * ‖kernel m d A₁ A₂ z j n
          ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ / (q * sqrtScale n) := by
  obtain ⟨T, hT, hb⟩ := uniform_leftMomentKernel_tail_bound hd h₁ h₂ hz hη hH m j k q
  refine ⟨T, hT, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn₀ a ha y hy hyH
  have hy₀ : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; linarith
  have hcurve : Continuous (fun t : ℝ =>
      (sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hcK := (differentiableOn_kernel hz m d A₁ A₂ j n).continuousOn.comp
    (s := Ioi a) hcurve.continuousOn (fun t ht =>
      Analytic.scaled_left_mem_kernelDomain h₁ h₂ n (sqrtScale_pos hn₀)
        (by have h := hT.trans ha; have hat : a < t := ht; linarith) hy₀)
  have hc := (by fun_prop : Continuous (fun t : ℝ =>
    (-(t : ℂ) + (y : ℂ) * Complex.I) ^ k)).continuousOn.mul hcK
  change ContinuousOn (leftMomentKernel m d A₁ A₂ z j n k y) (Ioi a) at hc
  exact integral_norm_le_shifted_exp_tail (mul_pos hq (sqrtScale_pos hn₀))
    (hc.aestronglyMeasurable measurableSet_Ioi)
    (fun t ht => by simpa only [neg_mul] using hn a ha t ht.le y hy hyH)

end ThisWork.Trajectory
