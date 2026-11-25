module

public import ThisWork.AsymmetricHankel
public import ThisWork.ParabolicHankel
public import ThisWork.HankelScaling

/-! Exact translation and positive-real scaling of improper Hankel integrals. -/

@[expose] public section
namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

theorem integral_comp_add_Iic (g : ℝ → ℂ) (a c : ℝ) :
    (∫ x in Iic a, g (x + c)) = ∫ x in Iic (a + c), g x := by
  calc
    _ = ∫ x : ℝ, ((Iic (a + c)).indicator g) (x + c) := by
      rw [← integral_indicator measurableSet_Iic]
      congr 1
      funext x
      simp only [indicator, mem_Iic, add_le_add_iff_right]
    _ = _ := by rw [integral_add_right_eq_self, integral_indicator measurableSet_Iic]

theorem integrableOn_comp_add_Iic {g : ℝ → ℂ} {a c : ℝ} (hg : IntegrableOn g (Iic (a + c))) :
    IntegrableOn (fun x => g (x + c)) (Iic a) := by
  have hg' := (integrable_indicator_iff measurableSet_Iic).mpr hg
  have hi := ((measurePreserving_add_right volume c).integrable_comp hg'.aestronglyMeasurable).mpr hg'
  rw [← integrable_indicator_iff measurableSet_Iic]
  convert hi using 1
  funext x
  simp only [Function.comp_apply, indicator, mem_Iic, add_le_add_iff_right]

theorem translated_integral_Iic (f : ℂ → ℂ) (a y : ℝ) (δ : ℂ) :
    (∫ u in Iic a, f (δ + (u : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ u in Iic (a + δ.re), f ((u : ℂ) + ((y + δ.im : ℝ) : ℂ) * Complex.I) := by
  rw [← integral_comp_add_Iic (fun u => f ((u : ℂ) + ((y + δ.im : ℝ) : ℂ) * Complex.I)) a δ.re]
  apply setIntegral_congr_fun measurableSet_Iic
  intro u _
  apply congrArg f
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem shiftedHankelIntegral_eq_asymmetric (right height : ℝ) (δ : ℂ) (f : ℂ → ℂ) :
    shiftedHankelIntegral right height δ f =
      asymmetricHankelIntegral (right + δ.re) (-height + δ.im) (height + δ.im) f := by
  have hlo := translated_integral_Iic f right (-height) δ
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hlo
  have hhi := translated_integral_Iic f right height δ
  have hv := intervalIntegral.integral_comp_add_right
    (fun y : ℝ => Complex.I * f (((right + δ.re : ℝ) : ℂ) + (y : ℂ) * Complex.I)) δ.im
    (a := -height) (b := height)
  have hint : (∫ y in -height..height, Complex.I * f (δ + (right : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in -height..height, Complex.I * f (((right + δ.re : ℝ) : ℂ) + ((y + δ.im : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y _
    apply congrArg (fun w : ℂ => Complex.I * f w)
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  dsimp only [shiftedHankelIntegral, asymmetricHankelIntegral]
  rw [hlo, hhi, hint, hv]

theorem shiftedHankelIntegral_eq_hankel (right height : ℝ) (δ : ℂ) (f : ℂ → ℂ) :
    shiftedHankelIntegral right height δ f = hankelIntegral right height (fun s => f (δ + s)) := by
  simp only [shiftedHankelIntegral, hankelIntegral, sub_eq_add_neg, add_assoc]

theorem shiftedHankelIntegral_scale (f : ℂ → ℂ) (right height : ℝ) (δ : ℂ)
    {R : ℝ} (hR : 0 < R) :
    shiftedHankelIntegral (R * right) (R * height) ((R : ℂ) * δ) f =
      (R : ℂ) * shiftedHankelIntegral right height δ (fun s => f ((R : ℂ) * s)) := by
  rw [shiftedHankelIntegral_eq_hankel, Analytic.hankelIntegral_scale _ _ _ hR,
    shiftedHankelIntegral_eq_hankel]
  congr 2
  funext s
  congr 1
  ring

end ThisWork
