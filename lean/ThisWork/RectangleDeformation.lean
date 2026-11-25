module

public import ThisWork.ContourConvergenceTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter MeasureTheory
open scoped Topology

theorem rectangle_integral_identity {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) {a r A B : ℝ}
    (hrect : ∀ z : ℂ, z.re ∈ uIcc a r → z.im ∈ uIcc A B → z ∈ U) :
    (∫ u in a..r, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
      (∫ u in a..r, f ((u : ℂ) + (B : ℂ) * Complex.I)) +
      (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) -
      (∫ v in A..B, Complex.I * f ((a : ℂ) + (v : ℂ) * Complex.I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + (A : ℂ) * Complex.I) ((r : ℂ) + (B : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add,
    smul_eq_mul, ← intervalIntegral.integral_const_mul] at h
  exact h (hf.mono fun z hz => hrect z hz.1 hz.2)

theorem horizontal_tail_identity_of_rectangles {f : ℂ → ℂ} {r A B : ℝ}
    (hA : IntegrableOn (fun u : ℝ => f ((u : ℂ) + (A : ℂ) * Complex.I)) (Iic r))
    (hB : IntegrableOn (fun u : ℝ => f ((u : ℂ) + (B : ℂ) * Complex.I)) (Iic r))
    (hleft : Tendsto (fun T : ℝ => ∫ v in A..B,
      Complex.I * f (-(T : ℂ) + (v : ℂ) * Complex.I)) atTop (𝓝 0))
    (hrect : ∀ᶠ T : ℝ in atTop,
      (∫ u in -T..r, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
        (∫ u in -T..r, f ((u : ℂ) + (B : ℂ) * Complex.I)) +
        (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) -
        (∫ v in A..B, Complex.I * f (-(T : ℂ) + (v : ℂ) * Complex.I)) = 0) :
    (∫ u in Iic r, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
      (∫ u in Iic r, f ((u : ℂ) + (B : ℂ) * Complex.I)) +
      (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) = 0 := by
  have h := (((intervalIntegral_tendsto_integral_Iic r hA tendsto_neg_atTop_atBot).sub
    (intervalIntegral_tendsto_integral_Iic r hB tendsto_neg_atTop_atBot)).add_const
      (∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I))).sub hleft
  simpa only [sub_zero] using tendsto_nhds_unique h (tendsto_const_nhds.congr' (hrect.mono fun _ hx => hx.symm))

theorem positive_height_strip {A B v : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hv : v ∈ uIcc A B) : 1 ≤ |v| ∧ |v| ≤ max A B := by
  have hv₁ : 1 ≤ v := (le_min hA hB).trans hv.1
  simpa only [abs_of_nonneg (show 0 ≤ v by linarith)] using And.intro hv₁ hv.2

theorem negative_height_strip {A B v : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hv : v ∈ uIcc (-A) (-B)) : 1 ≤ |v| ∧ |v| ≤ max A B := by
  have hn : -v ∈ uIcc A B := by
    rw [uIcc, mem_Icc, min_neg_neg, max_neg_neg] at hv
    exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
  simpa only [abs_neg] using positive_height_strip hA hB hn

end ThisWork.Analytic
