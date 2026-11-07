module

public import ThisWork.Argument
public import ThisWork.HankelDeformation

/-! Exact positive-real scaling identities for the original improper contours. -/

public section

namespace ThisWork.Analytic


open Set Filter MeasureTheory
open scoped Topology

theorem integral_comp_mul_left_Iic (g : ℝ → ℂ) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in Iic a, g (R * x)) = R⁻¹ • ∫ x in Iic (R * a), g x := by
  have hm : ∀ c : ℝ, MeasurableSet (Iic c) := fun _ => measurableSet_Iic
  rw [← integral_indicator (hm _), ← integral_indicator (hm _),
    ← abs_of_pos (inv_pos.mpr hR), ← Measure.integral_comp_mul_left]
  congr
  ext x
  rw [← indicator_comp_right, preimage_const_mul_Iic₀ _ hR, mul_div_cancel_left₀ _ hR.ne',
    Function.comp_def]

theorem integrableOn_comp_mul_left_Iic_iff (g : ℝ → ℂ) (a : ℝ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x => g (R * x)) (Iic a) ↔ IntegrableOn g (Iic (R * a)) := by
  rw [← integrable_indicator_iff measurableSet_Iic, ← integrable_indicator_iff measurableSet_Iic]
  convert integrable_comp_mul_left_iff ((Iic (R * a)).indicator g) hR.ne' using 2
  ext x
  rw [← indicator_comp_right, preimage_const_mul_Iic₀ _ hR, mul_div_cancel_left₀ _ hR.ne',
    Function.comp_def]

theorem scaled_integral_Iic (f : ℂ → ℂ) (r y : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ u in Iic (R * r), f ((u : ℂ) + ((R * y : ℝ) : ℂ) * Complex.I)) =
      (R : ℂ) * ∫ u in Iic r, f ((R : ℂ) * ((u : ℂ) + (y : ℂ) * Complex.I)) := by
  have hs := integral_comp_mul_left_Iic
    (fun u => f ((u : ℂ) + ((R * y : ℝ) : ℂ) * Complex.I)) r hR
  symm
  rw [← Complex.real_smul]
  calc
    _ = R • ∫ u in Iic r, f (((R * u : ℝ) : ℂ) + ((R * y : ℝ) : ℂ) * Complex.I) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Iic
      intro u _
      push_cast
      congr 1
      ring
    _ = _ := by rw [hs, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

theorem scaled_integral_vertical (f : ℂ → ℂ) (r a b R : ℝ) :
    (∫ v in R * a..R * b, Complex.I * f (((R * r : ℝ) : ℂ) + (v : ℂ) * Complex.I)) =
      (R : ℂ) * ∫ v in a..b, Complex.I * f ((R : ℂ) * ((r : ℂ) + (v : ℂ) * Complex.I)) := by
  calc
    _ = R • ∫ v in a..b, Complex.I *
        f (((R * r : ℝ) : ℂ) + ((R * v : ℝ) : ℂ) * Complex.I) :=
      (intervalIntegral.smul_integral_comp_mul_left
        (fun v : ℝ => Complex.I * f (((R * r : ℝ) : ℂ) + (v : ℂ) * Complex.I)) R).symm
    _ = _ := by
      rw [Complex.real_smul]
      congr 1
      apply intervalIntegral.integral_congr
      intro v _
      push_cast
      congr 2
      ring

theorem hankelIntegral_scale (f : ℂ → ℂ) (r h : ℝ) {R : ℝ} (hR : 0 < R) :
    hankelIntegral (R * r) (R * h) f =
      (R : ℂ) * hankelIntegral r h (fun s => f ((R : ℂ) * s)) := by
  have hlo := scaled_integral_Iic f r (-h) hR
  simp only [mul_neg, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hlo
  have hhi := scaled_integral_Iic f r h hR
  have hv := scaled_integral_vertical f r (-h) h R
  simp only [mul_neg] at hv
  simp only [hankelIntegral]
  rw [hlo, hhi, hv]
  ring

end ThisWork.Analytic
