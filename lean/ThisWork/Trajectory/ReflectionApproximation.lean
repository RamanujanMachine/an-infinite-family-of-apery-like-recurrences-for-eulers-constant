module

public import ThisWork.Trajectory.Reflection

/-! Quantitative approximation by the pole-free reflected kernel below the real axis. -/

public section

namespace ThisWork.Trajectory

/-- The reflection multiplier is close to one when the reflected exponential is small. -/
theorem norm_inv_sq_one_sub_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖1 / (1 - u) ^ 2 - 1‖ ≤ 10 * ‖u‖ := by
  have hden : 1 / 2 ≤ ‖1 - u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) u
    simp only [norm_one] at h
    linarith
  have hne : 1 - u ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖1 - u‖)
  have he : 1 / (1 - u) ^ 2 - 1 = (2 * u - u ^ 2) / (1 - u) ^ 2 := by
    field_simp
    ring
  have hnum : ‖2 * u - u ^ 2‖ ≤ (5 / 2 : ℝ) * ‖u‖ := by
    have h := norm_sub_le (2 * u) (u ^ 2)
    simp only [norm_mul, Complex.norm_ofNat, norm_pow] at h
    nlinarith [norm_nonneg u]
  rw [he, norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hne) 2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (show (1 / 4 : ℝ) ≤ ‖1 - u‖ ^ 2 by nlinarith)
    (norm_nonneg u)]

/-- Exponentially small relative error on a horizontal contour in the lower half-plane. -/
theorem norm_kernel_one_sub_reflected_le (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) {x : ℂ}
    (hx : x.im < 0) (hsmall : Real.exp (2 * Real.pi * x.im) ≤ 1 / 2) :
    ‖kernel m d A₁ A₂ z .one n x -
        (-4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x)‖ ≤
      10 * Real.exp (2 * Real.pi * x.im) *
        ‖-4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x‖ := by
  let A := -4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x
  rw [kernel_one_eq_reflected m d A₁ A₂ z n hx]
  change ‖A / (1 - Complex.exp (twist .two * x)) ^ 2 - A‖ ≤
    10 * Real.exp (2 * Real.pi * x.im) * ‖A‖
  rw [show A / (1 - Complex.exp (twist .two * x)) ^ 2 - A =
      A * (1 / (1 - Complex.exp (twist .two * x)) ^ 2 - 1) by ring, norm_mul]
  have hb := norm_inv_sq_one_sub_sub_one_le (u := Complex.exp (twist .two * x))
    (by simpa only [norm_exp_twist_two] using hsmall)
  rw [norm_exp_twist_two] at hb
  exact (mul_le_mul_of_nonneg_left hb (norm_nonneg A)).trans_eq (by ring)

end ThisWork.Trajectory
