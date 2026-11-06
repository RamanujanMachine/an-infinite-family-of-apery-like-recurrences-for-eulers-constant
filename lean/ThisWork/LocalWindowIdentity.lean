module

public import ThisWork.LocalSaddleExpansion
public import ThisWork.ContourWindows

/-! Exact parameter changes connecting the local Laplace integrals to contour windows. -/

@[expose] public section

namespace ThisWork

open Set MeasureTheory Filter

theorem rayIntegral_rescale (f : ℂ → ℂ) (σ v : ℂ) (d a b : ℝ) :
    (∫ u in a..b, ((d : ℂ) * v) * f (σ + (u : ℂ) * ((d : ℂ) * v))) =
      ∫ t in d * a..d * b, v * f (σ + (t : ℂ) * v) := by
  calc
    _ = (d : ℂ) * ∫ u in a..b, v * f (σ + ((d * u : ℝ) : ℂ) * v) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      push_cast
      rw [mul_assoc]
      congr 3
      ring
    _ = _ := by
      rw [← Complex.real_smul]
      exact intervalIntegral.smul_integral_comp_mul_left
        (fun t : ℝ => v * f (σ + (t : ℂ) * v)) d

theorem two_sided_rayIntegral_eq_window (f : ℂ → ℂ) (σ v : ℂ) (d cplus cminus : ℝ)
    (hminus : IntervalIntegrable (fun t : ℝ => v * f (σ + (t : ℂ) * v)) volume (-(d * cminus)) 0)
    (hplus : IntervalIntegrable (fun t : ℝ => v * f (σ + (t : ℂ) * v)) volume 0 (d * cplus)) :
    ((∫ u in 0..cplus, ((d : ℂ) * v) * f (σ + (u : ℂ) * ((d : ℂ) * v))) -
      (∫ u in 0..cminus, (-((d : ℂ) * v)) * f (σ + (u : ℂ) * (-((d : ℂ) * v))))) =
      ∫ t in -(d * cminus)..d * cplus, v * f (σ + (t : ℂ) * v) := by
  have hp := rayIntegral_rescale f σ v d 0 cplus
  have hm := rayIntegral_rescale f σ v (-d) 0 cminus
  simp only [mul_zero] at hp
  simp only [mul_zero, Complex.ofReal_neg, neg_mul] at hm
  simp only [neg_mul]
  rw [hp, hm, intervalIntegral.integral_symm (-(d * cminus)) 0]
  linear_combination intervalIntegral.integral_add_adjacent_intervals hminus hplus

theorem intervalIntegrable_ray_of_ball {f : ℂ → ℂ} {r a b : ℝ} {v : ℂ}
    (hv : ‖v‖ = 1) (hf : ContinuousOn f (Metric.ball 0 r))
    (hball : ∀ t ∈ uIcc a b, |t| < r) :
    IntervalIntegrable (fun t : ℝ => v * f ((t : ℂ) * v)) volume a b := by
  have hγ : Continuous (fun t : ℝ => (t : ℂ) * v) := Complex.continuous_ofReal.mul continuous_const
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.mul
  apply hf.comp hγ.continuousOn
  intro t ht
  simpa only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    hv, mul_one] using hball t ht

theorem two_sided_rayIntegral_eq_window_of_ball {f : ℂ → ℂ} {r d cplus cminus : ℝ} {v : ℂ}
    (hv : ‖v‖ = 1) (hd : 0 ≤ d) (hp : 0 ≤ cplus) (hm : 0 ≤ cminus)
    (hpr : d * cplus < r) (hmr : d * cminus < r) (hf : ContinuousOn f (Metric.ball 0 r)) :
    ((∫ u in 0..cplus, ((d : ℂ) * v) * f ((u : ℂ) * ((d : ℂ) * v))) -
      (∫ u in 0..cminus, (-((d : ℂ) * v)) * f ((u : ℂ) * (-((d : ℂ) * v))))) =
      ∫ t in -(d * cminus)..d * cplus, v * f ((t : ℂ) * v) := by
  apply (by simpa only [zero_add] using two_sided_rayIntegral_eq_window f 0 v d cplus cminus)
  · apply intervalIntegrable_ray_of_ball hv hf
    intro t ht
    rw [uIcc_of_le (neg_nonpos.mpr (mul_nonneg hd hm))] at ht
    have ht' : |t| ≤ d * cminus := abs_le.mpr ⟨ht.1, by linarith [ht.2, mul_nonneg hd hm]⟩
    exact ht'.trans_lt hmr
  · apply intervalIntegrable_ray_of_ball hv hf
    intro t ht
    rw [uIcc_of_le (mul_nonneg hd hp)] at ht
    simpa only [abs_of_nonneg ht.1] using ht.2.trans_lt hpr

namespace CompactSaddleFamily

theorem eventually_differentiableOn_localMomentKernel {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      DifferentiableOn ℂ (fun t => (t + S.saddle m) ^ k *
        kernel α₁ α₂ j (m + S.firstIndex)
          ((largeScale (m + S.firstIndex) : ℂ) * (t + S.saddle m)))
        (Metric.ball 0 (saddleScale α₁ α₂ / 16)) := by
  filter_upwards [(tendsto_add_atTop_nat S.firstIndex).eventually
    (eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j)] with m hm
  have hmap : MapsTo (fun t : ℂ => (largeScale (m + S.firstIndex) : ℂ) * (t + S.saddle m))
      (Metric.ball 0 (saddleScale α₁ α₂ / 16)) (kernelDomain α₁ α₂ (m + S.firstIndex)) := by
    intro t ht
    apply hm.2
    apply Metric.ball_subset_closedBall
    exact Metric.ball_subset_ball (by linarith [saddleScale_pos h₁ h₂] : saddleScale α₁ α₂ / 8 ≤ saddleScale α₁ α₂ / 4)
      (S.shifted_mem ht m)
  exact ((differentiableOn_id.add_const (S.saddle m)).pow k).mul
    ((differentiableOn_kernel α₁ α₂ j (m + S.firstIndex)).comp
      ((differentiableOn_id.add_const (S.saddle m)).const_mul _) hmap)

end CompactSaddleFamily

namespace CompactSaddleFamily.LocalSaddleData

noncomputable def localKernelMoment {α₁ α₂ : ℝ} {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (n : ℕ) (σ : ℂ) (k : ℕ) : ℂ :=
  (∫ u in 0..D.positive.cutoff, D.velocity *
    (((u : ℂ) * D.velocity + σ) ^ k *
      kernel α₁ α₂ j n ((largeScale n : ℂ) * ((u : ℂ) * D.velocity + σ)))) -
  (∫ u in 0..D.negative.cutoff, (-D.velocity) *
    (((u : ℂ) * (-D.velocity) + σ) ^ k *
      kernel α₁ α₂ j n ((largeScale n : ℂ) * ((u : ℂ) * (-D.velocity) + σ))))

theorem eventually_localKernelMoment_eq_phase {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (k : ℕ) :
    ∀ᶠ m : ℕ in Filter.atTop,
      D.localKernelMoment (m + D.shift + S.firstIndex) (S.saddle (m + D.shift)) k =
        kernel α₁ α₂ j (m + D.shift + S.firstIndex)
          ((largeScale (m + D.shift + S.firstIndex) : ℂ) * S.saddle (m + D.shift)) *
        D.localMoment (largeScale (m + D.shift + S.firstIndex)) k m := by
  filter_upwards [(tendsto_add_atTop_nat D.shift).eventually (S.eventually_kernel_eq_phase h₁ h₂)]
    with m hm
  let n := m + D.shift + S.firstIndex
  let σ := S.saddle (m + D.shift)
  have hhalf (v : ℂ) (c : ℝ)
      (hball : ∀ u ∈ uIcc 0 c, (u : ℂ) * v ∈ Metric.ball 0 (saddleScale α₁ α₂ / 16)) :
      (∫ u in 0..c, v * (((u : ℂ) * v + σ) ^ k *
        kernel α₁ α₂ j n ((largeScale n : ℂ) * ((u : ℂ) * v + σ)))) =
      kernel α₁ α₂ j n ((largeScale n : ℂ) * σ) *
        ∫ u in 0..c, v *
          (Complex.exp (-(largeScale n : ℂ) * S.phase ((u : ℂ) * v) (parameterShift D.shift m)) *
            S.momentAmplitude D.shift k ((u : ℂ) * v) m) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only [n, σ]
    rw [hm _ (hball u hu)]
    simp only [momentAmplitude, parameterShift_nat]
    ring
  simp only [localKernelMoment, localMoment, mul_sub]
  congr 1
  · exact hhalf _ _ (fun u hu => D.positive.inverseFamily.source_subset
      (D.positive.contour_in_source u
        (by simpa only [uIcc_of_le D.positive.cutoff_mem.1.le] using hu) m).1)
  · exact hhalf _ _ (fun u hu => D.negative.inverseFamily.source_subset
      (D.negative.contour_in_source u
        (by simpa only [uIcc_of_le D.negative.cutoff_mem.1.le] using hu) m).1)

theorem eventually_localKernelMoment_eq_rayWindow {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      D.localKernelMoment (m + D.shift + S.firstIndex) (S.saddle (m + D.shift)) k =
        ∫ t in -D.leftWidth..D.rightWidth, saddleTangent j *
          (((t : ℂ) * saddleTangent j + S.saddle (m + D.shift)) ^ k *
            kernel α₁ α₂ j (m + D.shift + S.firstIndex)
              ((largeScale (m + D.shift + S.firstIndex) : ℂ) *
                ((t : ℂ) * saddleTangent j + S.saddle (m + D.shift)))) := by
  filter_upwards [(tendsto_add_atTop_nat D.shift).eventually
    (S.eventually_differentiableOn_localMomentKernel h₁ h₂ k)] with m hm
  have he := two_sided_rayIntegral_eq_window_of_ball (norm_saddleTangent j) D.speed_pos.le
    D.positive.cutoff_mem.1.le D.negative.cutoff_mem.1.le D.widths_lt.2 D.widths_lt.1 hm.continuousOn
  simpa only [localKernelMoment, velocity, leftWidth, rightWidth] using he

end CompactSaddleFamily.LocalSaddleData

end ThisWork
