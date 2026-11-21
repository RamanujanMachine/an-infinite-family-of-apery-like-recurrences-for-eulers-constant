module

public import ThisWork.Trajectory.Contours

/-! Exact branch cancellation and Gamma reflection for the double-minimum regime. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Polynomial

/-- The two twists cancel to the sine-square factor used in the elementary mode. -/
theorem exp_twists_sub_two (x : ℂ) :
    Complex.exp (twist .one * x) + Complex.exp (twist .two * x) - 2 =
      -4 * Complex.sin ((Real.pi : ℂ) * x) ^ 2 := by
  calc
    _ = 2 * Complex.cos (2 * ((Real.pi : ℂ) * x)) - 2 := by
      rw [Complex.cos, twist_one, twist_two]
      ring_nf
    _ = _ := by rw [Complex.cos_two_mul_eq_one_sub]; ring

/-- The common untwisted kernel carries every branch twist. -/
theorem kernel_eq_twist (m d : ℕ) (A₁ A₂ z : ℝ) (j : Branch) (n : ℕ) (x : ℂ) :
    kernel m d A₁ A₂ z j n x =
      kernel m d A₁ A₂ z .three n x * Complex.exp (twist j * x) := by
  simp only [kernel, twist_three, zero_mul, Complex.exp_zero, mul_one]
  ring

theorem kernel_branch_cancellation (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (x : ℂ) :
    kernel m d A₁ A₂ z .one n x + kernel m d A₁ A₂ z .two n x -
      2 * kernel m d A₁ A₂ z .three n x =
      -4 * Complex.sin ((Real.pi : ℂ) * x) ^ 2 * kernel m d A₁ A₂ z .three n x := by
  rw [kernel_eq_twist m d A₁ A₂ z .one, kernel_eq_twist m d A₁ A₂ z .two]
  linear_combination kernel m d A₁ A₂ z .three n x * exp_twists_sub_two x

theorem sin_sq_mul_Gamma_sq {x : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * x) ^ 2 * Complex.Gamma x ^ 2 =
      (Real.pi : ℂ) ^ 2 / Complex.Gamma (1 - x) ^ 2 := by
  have hm := (eq_div_iff hs).mp (Complex.Gamma_mul_Gamma_one_sub x)
  have hG : Complex.Gamma (1 - x) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hm
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero hm.symm
  apply (eq_div_iff (pow_ne_zero 2 hG)).mpr
  calc
    _ = (Complex.Gamma x * Complex.Gamma (1 - x) * Complex.sin ((Real.pi : ℂ) * x)) ^ 2 := by ring
    _ = _ := congrArg (· ^ 2) hm

/-- The reflected kernel is holomorphic near the negative limiting saddle;
the original Gamma poles have been isolated into the sine factor. -/
noncomputable def reflectedKernel (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma ((d : ℂ) * n + x) * Complex.Gamma ((A₁ : ℂ) * n - x + 1) *
    Complex.Gamma ((A₂ : ℂ) * n - x + 1) / Complex.Gamma (1 - x) ^ 2 *
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - x))

theorem kernel_reflection (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) {x : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    -4 * Complex.sin ((Real.pi : ℂ) * x) ^ 2 * kernel m d A₁ A₂ z .three n x =
      -4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x := by
  have h := sin_sq_mul_Gamma_sq hs
  simp only [kernel, reflectedKernel, twist_three, zero_mul, Complex.exp_zero, mul_one]
  linear_combination -4 * Complex.Gamma ((d : ℂ) * n + x) *
    Complex.Gamma ((A₁ : ℂ) * n - x + 1) * Complex.Gamma ((A₂ : ℂ) * n - x + 1) *
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - x)) * h

theorem twist_factorization (x : ℂ) :
    Complex.exp (twist .one * x) * (1 - Complex.exp (twist .two * x)) ^ 2 =
      -4 * Complex.sin ((Real.pi : ℂ) * x) ^ 2 := by
  have he : Complex.exp (twist .one * x) * Complex.exp (twist .two * x) = 1 := by
    rw [← Complex.exp_add, twist_one, twist_two,
      show 2 * (Real.pi : ℂ) * Complex.I * x + -2 * (Real.pi : ℂ) * Complex.I * x = 0 by ring,
      Complex.exp_zero]
  linear_combination exp_twists_sub_two x + (Complex.exp (twist .two * x) - 2) * he

theorem kernel_one_mul_denominator (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) {x : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    kernel m d A₁ A₂ z .one n x * (1 - Complex.exp (twist .two * x)) ^ 2 =
      -4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x := by
  rw [kernel_eq_twist m d A₁ A₂ z .one, mul_assoc, twist_factorization, mul_comm]
  exact kernel_reflection m d A₁ A₂ z n hs

theorem norm_exp_twist_two (x : ℂ) :
    ‖Complex.exp (twist .two * x)‖ = Real.exp (2 * Real.pi * x.im) := by
  simp [twist_two, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- In the lower half-plane the growing branch is an analytic reflected kernel
times a multiplier that tends exponentially to one with the contour height. -/
theorem kernel_one_eq_reflected (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) {x : ℂ}
    (hx : x.im < 0) :
    kernel m d A₁ A₂ z .one n x =
      (-4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x) /
        (1 - Complex.exp (twist .two * x)) ^ 2 := by
  have hn : ‖Complex.exp (twist .two * x)‖ < 1 := by
    rw [norm_exp_twist_two]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (by positivity) hx)
  have hden : 1 - Complex.exp (twist .two * x) ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_one] at he
    linarith
  have hs : Complex.sin ((Real.pi : ℂ) * x) ≠ 0 := by
    intro h
    have hf := twist_factorization x
    rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hf
    exact mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero 2 hden) hf
  exact (eq_div_iff (pow_ne_zero 2 hden)).mpr (kernel_one_mul_denominator m d A₁ A₂ z n hs)

theorem Gamma_right_nat_ratio (B n : ℕ) {x : ℂ}
    (hx : ∀ k : ℕ, 1 - x ≠ -k) :
    Complex.Gamma ((B : ℂ) * n - x + 1) / Complex.Gamma (1 - x) =
      (ascPochhammer ℂ (B * n)).eval (1 - x) := by
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := B * n) (1 - x) hx
  rw [show (1 - x) + (B * n : ℕ) = (B : ℂ) * n - x + 1 by push_cast; ring] at h
  exact h

/-- For the integer slopes in `T₃`, reflection leaves just one Gamma factor
and two explicit polynomials. -/
theorem reflectedKernel_eq_polynomial (m d B₁ B₂ : ℕ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : ∀ k : ℕ, 1 - x ≠ -k) :
    reflectedKernel m d (B₁ : ℝ) (B₂ : ℝ) z n x =
      Complex.Gamma ((d : ℂ) * n + x) *
        (ascPochhammer ℂ (B₁ * n)).eval (1 - x) *
        (ascPochhammer ℂ (B₂ * n)).eval (1 - x) *
        Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - x)) := by
  calc
    _ = Complex.Gamma ((d : ℂ) * n + x) *
        (Complex.Gamma ((B₁ : ℂ) * n - x + 1) / Complex.Gamma (1 - x)) *
        (Complex.Gamma ((B₂ : ℂ) * n - x + 1) / Complex.Gamma (1 - x)) *
        Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - x)) := by
      simp only [reflectedKernel, Complex.ofReal_natCast]
      ring
    _ = _ := by rw [Gamma_right_nat_ratio B₁ n hx, Gamma_right_nat_ratio B₂ n hx]

end ThisWork.Trajectory
