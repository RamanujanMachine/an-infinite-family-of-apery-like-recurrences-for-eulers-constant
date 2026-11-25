module

public import ThisWork.ReflectedBoundary
public import ThisWork.ReflectedDigamma

/-! Quantitative separation of the two banks of the reflected boundary mode.
On the lower bank the regular reflected kernel is the main term; on the upper
bank the multiplier is exponentially small. -/

@[expose] public section
namespace ThisWork

theorem boundaryKernel_eq_cot {r : ℕ} (hr : 0 < r) (b : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    boundaryKernel r b A z n x =
      (Real.pi : ℂ) * (Complex.cot ((Real.pi : ℂ) * x) + Complex.I) *
        reflectedKernel r b A z n x := by
  rw [boundaryKernel_eq_reflected hr b A z n hx]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * x = ((Real.pi : ℂ) * x) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cot]
  field_simp

theorem norm_boundaryKernel_upper_le {r : ℕ} (hr : 0 < r) (b : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0)
    (he : Real.exp (-2 * Real.pi * x.im) ≤ 1 / 2) :
    ‖boundaryKernel r b A z n x‖ ≤
      4 * Real.pi * Real.exp (-2 * Real.pi * x.im) * ‖reflectedKernel r b A z n x‖ := by
  rw [boundaryKernel_eq_cot hr b A z n hx, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h := mul_le_mul_of_nonneg_left (Analytic.norm_cot_pi_add_I_le he) Real.pi_pos.le
  nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (reflectedKernel r b A z n x))]

theorem norm_boundaryKernel_lower_error_le {r : ℕ} (hr : 0 < r) (b : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0)
    (he : Real.exp (2 * Real.pi * x.im) ≤ 1 / 2) :
    ‖boundaryKernel r b A z n x -
      2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r b A z n x‖ ≤
      4 * Real.pi * Real.exp (2 * Real.pi * x.im) * ‖reflectedKernel r b A z n x‖ := by
  rw [boundaryKernel_eq_cot hr b A z n hx]
  have hid : (Real.pi : ℂ) * (Complex.cot ((Real.pi : ℂ) * x) + Complex.I) *
      reflectedKernel r b A z n x - 2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r b A z n x =
      (Real.pi : ℂ) * (Complex.cot ((Real.pi : ℂ) * x) - Complex.I) *
        reflectedKernel r b A z n x := by ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h := mul_le_mul_of_nonneg_left (Analytic.norm_cot_pi_sub_I_le he) Real.pi_pos.le
  nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (reflectedKernel r b A z n x))]

end ThisWork
