module

public import ThisWork.Trajectory.HankelCongruence

/-! Real translations of the polygonal Hankel contour. -/

@[expose] public section

namespace ThisWork.Analytic

open Set MeasureTheory

theorem integral_Iic_comp_add (f : ℝ → ℂ) (r a : ℝ) :
    (∫ u in Iic r, f (u + a)) = ∫ u in Iic (r + a), f u := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have he : (fun u => (Iic r).indicator (fun v => f (v + a)) u) =
      (fun u => (Iic (r + a)).indicator f (u + a)) := by
    funext u
    simp only [Set.indicator, mem_Iic, add_le_add_iff_right]
  rw [he, integral_add_right_eq_self]

theorem hankelIntegral_translate (r h a : ℝ) (f : ℂ → ℂ) :
    hankelIntegral r h (fun x => f (x + (a : ℂ))) = hankelIntegral (r + a) h f := by
  unfold hankelIntegral
  simp_rw [show ∀ u : ℝ, (u : ℂ) - (h : ℂ) * Complex.I + (a : ℂ) =
      ((u + a : ℝ) : ℂ) - (h : ℂ) * Complex.I by intro u; push_cast; ring,
    show ∀ u : ℝ, (u : ℂ) + (h : ℂ) * Complex.I + (a : ℂ) =
      ((u + a : ℝ) : ℂ) + (h : ℂ) * Complex.I by intro u; push_cast; ring]
  rw [integral_Iic_comp_add (fun u : ℝ => f ((u : ℂ) - (h : ℂ) * Complex.I)) r a,
    integral_Iic_comp_add (fun u : ℝ => f ((u : ℂ) + (h : ℂ) * Complex.I)) r a]
  congr 2
  apply intervalIntegral.integral_congr
  intro v hv
  apply congrArg (fun w : ℂ => Complex.I * f w)
  push_cast
  ring

end ThisWork.Analytic
