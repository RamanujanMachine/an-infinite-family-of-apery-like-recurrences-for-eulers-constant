module

public import ThisWork.HankelScaling

/-! Exact truncation of the two infinite horizontal contour pieces. -/

@[expose] public section

namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

noncomputable def finiteHankelIntegral (left right height : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ u in left..right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
    (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
    ∫ u in left..right, f ((u : ℂ) + (height : ℂ) * Complex.I)

theorem hankelIntegral_eq_truncation {f : ℂ → ℂ} {left right height : ℝ}
    (hlr : left ≤ right)
    (hlo : IntegrableOn (fun u : ℝ => f ((u : ℂ) - (height : ℂ) * Complex.I)) (Iic right))
    (hhi : IntegrableOn (fun u : ℝ => f ((u : ℂ) + (height : ℂ) * Complex.I)) (Iic right)) :
    hankelIntegral right height f = finiteHankelIntegral left right height f +
      (∫ u in Iic left, f ((u : ℂ) - (height : ℂ) * Complex.I)) -
      ∫ u in Iic left, f ((u : ℂ) + (height : ℂ) * Complex.I) := by
  have hb := intervalIntegral.integral_Iic_sub_Iic
    (hlo.mono_set (Iic_subset_Iic.mpr hlr)) hlo
  have ht := intervalIntegral.integral_Iic_sub_Iic
    (hhi.mono_set (Iic_subset_Iic.mpr hlr)) hhi
  simp only [hankelIntegral, finiteHankelIntegral]
  rw [← hb, ← ht]
  ring

theorem norm_hankelIntegral_sub_truncation {f : ℂ → ℂ} {left right height : ℝ}
    (hlr : left ≤ right)
    (hlo : IntegrableOn (fun u : ℝ => f ((u : ℂ) - (height : ℂ) * Complex.I)) (Iic right))
    (hhi : IntegrableOn (fun u : ℝ => f ((u : ℂ) + (height : ℂ) * Complex.I)) (Iic right)) :
    ‖hankelIntegral right height f - finiteHankelIntegral left right height f‖ ≤
      ‖∫ u in Iic left, f ((u : ℂ) - (height : ℂ) * Complex.I)‖ +
      ‖∫ u in Iic left, f ((u : ℂ) + (height : ℂ) * Complex.I)‖ := by
  rw [hankelIntegral_eq_truncation hlr hlo hhi]
  convert norm_sub_le
    (∫ u in Iic left, f ((u : ℂ) - (height : ℂ) * Complex.I))
    (∫ u in Iic left, f ((u : ℂ) + (height : ℂ) * Complex.I)) using 1
  congr 1
  ring

end ThisWork
