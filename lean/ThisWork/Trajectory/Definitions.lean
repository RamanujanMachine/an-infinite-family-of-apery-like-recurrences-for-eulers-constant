module

public import ThisWork.Definitions

/-! Mellin–Barnes integrals for lower slopes `(m,m,m+d)`.
The parameters `Aᵢ = m-aᵢ` and the positive real argument `z` are kept symbolic.
No asymptotic property is assumed in these definitions. -/

@[expose] public section

namespace ThisWork.Trajectory

/-- The actual kernel after `x = mn-s`, with the full Meijer G argument factor. -/
noncomputable def kernel (m d : ℕ) (A₁ A₂ z : ℝ) (j : Branch)
    (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma x ^ 2 * Complex.Gamma ((d : ℂ) * n + x) *
    Complex.Gamma ((A₁ : ℂ) * n - x + 1) *
    Complex.Gamma ((A₂ : ℂ) * n - x + 1) * Complex.exp (twist j * x) *
    Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - x))

/-- The same reference Hankel contour as in Lemma 8. -/
noncomputable def branchIntegral (m d : ℕ) (A₁ A₂ z : ℝ)
    (j : Branch) (n : ℕ) : Fin 3 → ℂ := fun k =>
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z j n x)

/-- The common Gamma and argument factor when all three lower slopes agree. -/
noncomputable def equalScale (m : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) : ℝ :=
  gammaScale A₁ A₂ n * z ^ (m * n)

/-- The common factor when exactly two lower slopes attain the minimum. -/
noncomputable def doubleScale (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma ((d : ℝ) * n) * equalScale m A₁ A₂ z n

/-- The square-root saddle coefficient in the double-minimum regime. -/
noncomputable def doubleSaddleScale (d : ℕ) (A₁ A₂ z : ℝ) : ℝ :=
  Real.sqrt (A₁ * A₂ * z / d)

/-- The elementary mode exposed by the exact branch cancellation. -/
noncomputable def elementaryIntegral (m d : ℕ) (A₁ A₂ z : ℝ)
    (n : ℕ) : Fin 3 → ℂ :=
  branchIntegral m d A₁ A₂ z .one n + branchIntegral m d A₁ A₂ z .two n -
    2 • branchIntegral m d A₁ A₂ z .three n

@[simp] theorem kernel_one_zero (A₁ A₂ z : ℝ) (j : Branch) (n : ℕ) (x : ℂ) :
    kernel 1 0 A₁ A₂ z j n x = ThisWork.kernel A₁ A₂ z j n x := by
  simp only [kernel, ThisWork.kernel, Nat.cast_zero, zero_mul, zero_add,
    Nat.cast_one, one_mul, pow_succ]

@[simp] theorem branchIntegral_one_zero (A₁ A₂ z : ℝ) (j : Branch) (n : ℕ) :
    branchIntegral 1 0 A₁ A₂ z j n = ThisWork.branchIntegral A₁ A₂ z j n := by
  unfold branchIntegral ThisWork.branchIntegral
  simp only [kernel_one_zero, Nat.cast_one, one_mul]

theorem doubleSaddleScale_pos {d : ℕ} {A₁ A₂ z : ℝ} (hd : 0 < d)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    0 < doubleSaddleScale d A₁ A₂ z :=
  Real.sqrt_pos.mpr (div_pos (mul_pos (mul_pos h₁ h₂) hz) (Nat.cast_pos.mpr hd))

theorem doubleSaddleScale_sq {d : ℕ} {A₁ A₂ z : ℝ} (hd : 0 < d)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    doubleSaddleScale d A₁ A₂ z ^ 2 = A₁ * A₂ * z / d :=
  Real.sq_sqrt (div_pos (mul_pos (mul_pos h₁ h₂) hz) (Nat.cast_pos.mpr hd)).le

end ThisWork.Trajectory
