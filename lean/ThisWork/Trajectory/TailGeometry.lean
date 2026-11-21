module

public import ThisWork.Trajectory.SqrtParameters
public import ThisWork.UniformTailDerivative

/-! Uniform geometry of the moving Gamma factor, including its transition at `x ≈ -dn`. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter
open scoped Topology

/-- A constant covering the near, transition, and far regions of the left tail. -/
noncomputable def tailGeometryConstant (d η : ℝ) : ℝ :=
  max (2 * (d + 1) ^ 2) (max (2 * (1 + 2 * d) ^ 2 / η) 8)

/-- The moving factor cannot become too small relative to both right-hand factors.
The imaginary part controls the transition where the real part changes sign. -/
theorem tail_geometry {d R t q η : ℝ} (hd : 1 ≤ d) (hR : 1 ≤ R) (ht : 1 ≤ t)
    (hη : 0 < η) (hqη : η ≤ q) (hq : |d * R - t| ≤ q) :
    (R + t) ^ 2 ≤ tailGeometryConstant d η * R * t * q := by
  have hq0 : 0 ≤ q := hη.le.trans hqη
  have hC₁ : 2 * (d + 1) ^ 2 ≤ tailGeometryConstant d η := le_max_left _ _
  have hC₂ : 2 * (1 + 2 * d) ^ 2 / η ≤ tailGeometryConstant d η :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC₃ : 8 ≤ tailGeometryConstant d η :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases hnear : t ≤ d * R / 2
  · have hqR : R / 2 ≤ q := by
      have h := (le_abs_self (d * R - t)).trans hq
      nlinarith [mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ R)]
    have hprod : R ≤ 2 * t * q := by
      nlinarith [mul_le_mul_of_nonneg_right ht hq0]
    calc
      _ ≤ ((d + 1) * R) ^ 2 := by gcongr; nlinarith
      _ = (d + 1) ^ 2 * R * R := by ring
      _ ≤ (d + 1) ^ 2 * R * (2 * t * q) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (2 * (d + 1) ^ 2) * R * t * q := by ring
      _ ≤ _ := by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hC₁ (by positivity : 0 ≤ R * t * q)
  · by_cases hfar : 2 * d * R ≤ t
    · have hRt : R ≤ t := by
        nlinarith [mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ R)]
      have hqhalf : t / 2 ≤ q := by
        have h := (neg_le_abs (d * R - t)).trans hq
        linarith
      calc
        _ ≤ (2 * t) ^ 2 := by gcongr; linarith
        _ = 8 * 1 * t * (t / 2) := by ring
        _ ≤ 8 * R * t * q := by gcongr
        _ ≤ _ := by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hC₃ (by positivity : 0 ≤ R * t * q)
    · have hhalf : R / 2 ≤ t := by nlinarith [mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ R)]
      calc
        _ ≤ ((1 + 2 * d) * R) ^ 2 := by gcongr; linarith
        _ = (2 * (1 + 2 * d) ^ 2 / η) * R * (R / 2) * η := by field_simp
        _ ≤ (2 * (1 + 2 * d) ^ 2 / η) * R * t * q := by gcongr
        _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC₂ (by positivity : 0 ≤ R * t * q)

/-- A refined bound retains the crossover between `n` and `sqrt(n)*t`. -/
theorem norm_right_factor_sqrt_tail_le {A R t y H : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hR : 1 ≤ R) (hsq : R ^ 2 = (n : ℝ)) (ht : 1 ≤ t) (hy : |y| ≤ H) :
    ‖(A : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ ≤
      (A + H + 2) * R * (R + t) := by
  rw [show (A : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1 =
    ((A * n + R * t + 1 : ℝ) : ℂ) + ((-R * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  calc
    _ ≤ ‖((A * n + R * t + 1 : ℝ) : ℂ)‖ + ‖((-R * y : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = A * n + R * t + 1 + R * |y| := by
      rw [Complex.norm_of_nonneg (show 0 ≤ A * n + R * t + 1 by positivity)]
      simp [abs_of_nonneg (show 0 ≤ R by linarith)]
    _ ≤ (A + H + 2) * R * (R + t) := by
      have hH : 0 ≤ H := (abs_nonneg y).trans hy
      rw [← hsq]
      nlinarith [mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ R),
        mul_nonneg hH (mul_nonneg (by linarith : 0 ≤ R) (sub_nonneg.mpr hR)),
        mul_nonneg (show 0 ≤ A + H + 1 by positivity)
          (mul_nonneg (by linarith : 0 ≤ R) (by linarith : 0 ≤ t)), sq_nonneg (R - 1)]

end ThisWork.Trajectory
