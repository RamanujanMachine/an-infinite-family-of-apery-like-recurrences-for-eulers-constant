module

public import ThisWork.Argument
public import ThisWork.UniformWeightedTails
public import ThisWork.AbsoluteConvergence

/-! Integral estimates for the infinite parts of the actual moving contours. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory
open scoped Topology

theorem integral_norm_le_exp_tail {f : ℝ → ℂ} {C a T : ℝ} (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi T)))
    (hb : ∀ t ∈ Ioi T, ‖f t‖ ≤ C * Real.exp (-a * t)) :
    IntegrableOn f (Ioi T) ∧
      ‖∫ t in Ioi T, f t‖ ≤ C * Real.exp (-a * T) / a := by
  have hg : IntegrableOn (fun t => C * Real.exp (-a * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) T).const_mul C
  have hfa : IntegrableOn f (Ioi T) := hg.mono' hf
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hb t ht)
  refine ⟨hfa, ?_⟩
  calc
    _ ≤ ∫ t in Ioi T, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, C * Real.exp (-a * t) :=
      integral_mono_ae hfa.norm hg ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hb t ht)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
      ring

noncomputable def scaledLeftWeightedKernel [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n k : ℕ)
    (y t : ℝ) : ℂ :=
  ((n : ℂ) - (largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) ^ k *
    normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))

theorem uniform_integrated_weighted_tail [PositiveArgument] {α₁ α₂ η H q : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hη : 0 < η) (hH : 0 ≤ H) (hq : 0 < q)
    (j : Branch) (k : ℕ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      IntegrableOn (scaledLeftWeightedKernel α₁ α₂ j n k y) (Ioi T) ∧
      ‖∫ t in Ioi T, scaledLeftWeightedKernel α₁ α₂ j n k y t‖ ≤
        (n : ℝ) ^ k * ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
          Real.exp (-q * largeScale n * T) / (q * largeScale n) := by
  obtain ⟨T, hT, hb⟩ := uniform_weighted_kernel_normalized_far_tail h₁ h₂ hη hH j k q
  refine ⟨T, hT, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 σ hσ y hy hyH
  have hy0 : y ≠ 0 := by intro he; simp only [he, abs_zero] at hy; linarith
  have hcurve : Continuous (fun t : ℝ =>
      (largeScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
  have hc := (continuousOn_weighted_kernel α₁ α₂ j n k).comp
    (s := Ioi T) hcurve.continuousOn
    (fun t ht => scaled_left_mem_kernelDomain h₁ h₂ n (largeScale_pos hn0)
      (lt_of_lt_of_le zero_lt_one (hT.trans ht.le)) hy0)
  change ContinuousOn (scaledLeftWeightedKernel α₁ α₂ j n k y) (Ioi T) at hc
  simpa only [neg_mul] using integral_norm_le_exp_tail
    (mul_pos hq (largeScale_pos hn0)) (hc.aestronglyMeasurable measurableSet_Ioi)
    (fun t ht => by
      simpa only [scaledLeftWeightedKernel, neg_mul] using hn σ hσ t ht.le y hy hyH)

end ThisWork.Analytic
