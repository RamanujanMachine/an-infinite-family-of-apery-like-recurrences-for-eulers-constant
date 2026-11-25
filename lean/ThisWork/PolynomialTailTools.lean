module

public import ThisWork.GammaTailBounds

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric MeasureTheory
open scoped Topology

theorem log_norm_sine_tail_lower {z : ℂ} (hz : 1 ≤ |z.im|) :
    -Real.log 4 ≤ Real.log ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have him : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos]
  have hs := abs_log_norm_sin_sub_abs_im (z := (Real.pi : ℂ) * z)
    (by simpa only [him, mul_assoc] using sine_tail_exp_bound hz)
  rw [him] at hs
  nlinarith [(abs_le.mp hs).1, mul_nonneg Real.pi_pos.le (abs_nonneg z.im)]

theorem eventually_shifted_pow_le_exp {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    ∀ᶠ T : ℝ in atTop, (T + D) ^ k ≤ Real.exp T := by
  have h := (Real.isLittleO_pow_exp_atTop (n := k)).const_mul_left ((1 + D) ^ k)
  filter_upwards [h.def zero_lt_one, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
  calc
    (T + D) ^ k ≤ ((1 + D) * T) ^ k := pow_le_pow_left₀ (by linarith)
      (by nlinarith [mul_le_mul_of_nonneg_left hT₁ hD]) k
    _ = (1 + D) ^ k * T ^ k := mul_pow _ _ _
    _ ≤ Real.exp T := by simpa only [Real.norm_of_nonneg (by positivity :
      0 ≤ (1 + D) ^ k * T ^ k), Real.norm_of_nonneg (Real.exp_pos T).le, one_mul] using hT

theorem norm_polynomial_left_le {T y H : ℝ} (hT : 0 ≤ T) (hy : |y| ≤ H) (n : ℕ) :
    ‖(n : ℂ) - (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ T + ((n : ℝ) + H) := by
  calc
    _ ≤ ‖(n : ℂ)‖ + ‖-(T : ℂ) + (y : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ ≤ ‖(n : ℂ)‖ + (‖-(T : ℂ)‖ + ‖(y : ℂ) * Complex.I‖) :=
      add_le_add (le_refl _) (norm_add_le _ _)
    _ = (n : ℝ) + (T + |y|) := by simp [abs_of_nonneg hT]
    _ ≤ T + ((n : ℝ) + H) := by linarith

end ThisWork.Analytic
