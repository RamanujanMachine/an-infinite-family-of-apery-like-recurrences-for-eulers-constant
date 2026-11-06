module

public import ThisWork.FiniteRemainderBound
public import ThisWork.MomentTailBounds

/-! Uniform exponentially small remainders for the complete improper contours. -/

public section

namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

theorem integrableOn_Iic_of_reflected_tail {f : ℝ → ℂ} {r T : ℝ}
    (hf : ContinuousOn f (Iic r))
    (ht : IntegrableOn (fun t => f (-t)) (Ioi T)) : IntegrableOn f (Iic r) := by
  have hleft : IntegrableOn f (Iio (-T)) := by
    simpa only [Set.neg_Ioi, neg_neg] using ht.comp_neg
  exact integrableOn_Iic_iff_integrableAtFilter_atBot.mpr
    ⟨⟨Iio (-T), Iio_mem_atBot _, hleft⟩, hf.locallyIntegrableOn measurableSet_Iic⟩

theorem uniform_hankel_truncation_moment_bound {α₁ α₂ q : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hq : 0 < q) (j : Branch) (k : ℕ) :
    ∃ T ≥ 1, 2 * saddleScale α₁ α₂ ≤ T ∧
      ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖hankelIntegral (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)
          (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s)) -
        finiteHankelIntegral (-T) (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)
          (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s))‖ ≤
        2 * (‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
          Real.exp (-q * largeScale n * T) / (q * largeScale n)) := by
  have hc := saddleScale_pos h₁ h₂
  obtain ⟨A, hA, hbnd⟩ := uniform_integrated_moment_tail_cutoffs h₁ h₂
    (η := saddleScale α₁ α₂ / 4) (H := 2 * saddleScale α₁ α₂)
    (by positivity) (by positivity) hq j k
  let T := max A (max 1 (2 * saddleScale α₁ α₂))
  have hTA : A ≤ T := le_max_left _ _
  have hT1 : 1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTc : 2 * saddleScale α₁ α₂ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, hT1, hTc, ?_⟩
  filter_upwards [hbnd, eventually_continuousOn_moment_kernel_contour h₁ h₂ j k]
    with n hn hcont σ hσ
  have hh := saddleContourHeight_bounds hc j hσ
  have hh0 : 0 ≤ saddleContourHeight (saddleScale α₁ α₂) j σ := by linarith
  have hu := hn σ hσ T hTA (saddleContourHeight (saddleScale α₁ α₂) j σ)
    (by simpa only [abs_of_nonneg hh0] using hh.1)
    (by simpa only [abs_of_nonneg hh0] using hh.2)
  have hl := hn σ hσ T hTA (-saddleContourHeight (saddleScale α₁ α₂) j σ)
    (by simpa only [abs_neg, abs_of_nonneg hh0] using hh.1)
    (by simpa only [abs_neg, abs_of_nonneg hh0] using hh.2)
  let r := saddleContourRight (saddleScale α₁ α₂) j σ
  let h := saddleContourHeight (saddleScale α₁ α₂) j σ
  let f : ℂ → ℂ := fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s)
  have hct : ContinuousOn f (hankelTrace r h) := hcont σ hσ
  have hel : (fun u : ℝ => f (((-u : ℝ) : ℂ) - (h : ℂ) * Complex.I)) =
      scaledLeftMomentKernel α₁ α₂ j n k (-h) := by
    funext u
    dsimp only [f, scaledLeftMomentKernel]
    simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]
  have heu : (fun u : ℝ => f (((-u : ℝ) : ℂ) + (h : ℂ) * Complex.I)) =
      scaledLeftMomentKernel α₁ α₂ j n k h := by
    funext u
    dsimp only [f, scaledLeftMomentKernel]
    simp only [Complex.ofReal_neg]
  have hli : IntegrableOn (fun u : ℝ => f (((-u : ℝ) : ℂ) - (h : ℂ) * Complex.I)) (Ioi T) := by
    rw [hel]
    exact hl.1
  have hui : IntegrableOn (fun u : ℝ => f (((-u : ℝ) : ℂ) + (h : ℂ) * Complex.I)) (Ioi T) := by
    rw [heu]
    exact hu.1
  have il := integrableOn_Iic_of_reflected_tail (continuousOn_lower_of_continuousTrace hct) hli
  have iu := integrableOn_Iic_of_reflected_tail (continuousOn_upper_of_continuousTrace hct) hui
  have hnl := hl.2
  have hnu := hu.2
  change ‖∫ t in Ioi T, scaledLeftMomentKernel α₁ α₂ j n k (-h) t‖ ≤ _ at hnl
  change ‖∫ t in Ioi T, scaledLeftMomentKernel α₁ α₂ j n k h t‖ ≤ _ at hnu
  rw [← hel, integral_comp_neg_Ioi T (fun u : ℝ => f ((u : ℂ) - (h : ℂ) * Complex.I))] at hnl
  rw [← heu, integral_comp_neg_Ioi T (fun u : ℝ => f ((u : ℂ) + (h : ℂ) * Complex.I))] at hnu
  have htrunc := norm_hankelIntegral_sub_truncation
    (left := -T) (by dsimp only [r]; linarith [(saddleContourRight_bounds hc j hσ).1]) il iu
  exact htrunc.trans (by linarith)

theorem uniform_full_window_remainder_bound {α₁ α₂ a b : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < saddleScale α₁ α₂ / 16) (hb : b < saddleScale α₁ α₂ / 16)
    (j : Branch) (D : ℝ) (k : ℕ) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ‖hankelIntegral (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)
          (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s)) -
        contourWindow j σ a b (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)
          (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s))‖ ≤
        C * ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-ε * largeScale n) := by
  have hc := saddleScale_pos h₁ h₂
  obtain ⟨T, hT1, hTc, htail⟩ := uniform_hankel_truncation_moment_bound h₁ h₂ (q := 1) (by norm_num) j k
  obtain ⟨ε, hε, hfinite⟩ := uniform_finite_window_remainder_bound h₁ h₂ ha0 hb0 hTc ha hb j D k
  let q := min ε 1
  let B := 4 * (T + 4 * saddleScale α₁ α₂) ^ k * (2 * T + 8 * saddleScale α₁ α₂)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨q, lt_min hε zero_lt_one, B + 2, by positivity, ?_⟩
  filter_upwards [htail, hfinite, largeScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with n htn hfn hR σ hσ hdisp
  have hR0 : 0 ≤ largeScale n := by linarith
  have hefin : Real.exp (-ε * largeScale n) ≤ Real.exp (-q * largeScale n) :=
    Real.exp_le_exp.mpr (by
      dsimp only [q]
      nlinarith [mul_le_mul_of_nonneg_right (min_le_left ε 1) hR0])
  have heT : Real.exp (-largeScale n * T) ≤ Real.exp (-q * largeScale n) :=
    Real.exp_le_exp.mpr (by
      have hqT : q ≤ T := (min_le_right ε 1).trans hT1
      nlinarith [mul_le_mul_of_nonneg_left hqT hR0])
  let K := ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖
  let H := hankelIntegral (saddleContourRight (saddleScale α₁ α₂) j σ)
    (saddleContourHeight (saddleScale α₁ α₂) j σ)
    (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s))
  let F := finiteHankelIntegral (-T) (saddleContourRight (saddleScale α₁ α₂) j σ)
    (saddleContourHeight (saddleScale α₁ α₂) j σ)
    (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s))
  let W := contourWindow j σ a b (saddleContourRight (saddleScale α₁ α₂) j σ)
    (saddleContourHeight (saddleScale α₁ α₂) j σ)
    (fun s => s ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * s))
  have hquot : K * Real.exp (-largeScale n * T) / largeScale n ≤ K * Real.exp (-q * largeScale n) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left heT (norm_nonneg _)) hR0).trans
      (div_le_self (by positivity) hR)
  have ht1 : ‖H - F‖ ≤ 2 * K * Real.exp (-q * largeScale n) := by
    calc
      _ ≤ 2 * (K * Real.exp (-largeScale n * T) / largeScale n) := by
        simpa only [neg_one_mul, one_mul] using htn σ hσ
      _ ≤ 2 * (K * Real.exp (-q * largeScale n)) := mul_le_mul_of_nonneg_left hquot (by norm_num)
      _ = _ := by ring
  have hf1 : ‖F - W‖ ≤ B * K * Real.exp (-q * largeScale n) := by
    calc
      _ ≤ 4 * ((T + 4 * saddleScale α₁ α₂) ^ k * K * Real.exp (-ε * largeScale n)) *
          (2 * T + 8 * saddleScale α₁ α₂) := hfn σ hσ hdisp
      _ = B * K * Real.exp (-ε * largeScale n) := by dsimp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hefin (by positivity)
  have htri := norm_add_le (H - F) (F - W)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans ((add_le_add ht1 hf1).trans_eq (by ring))

end ThisWork
