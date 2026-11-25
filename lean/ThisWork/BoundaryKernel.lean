module

public import ThisWork.BoundaryFourier

/-! Exact identities connecting the even-rank Fourier family and its
reflected auxiliary kernel. -/

@[expose] public section
namespace ThisWork

noncomputable def boundaryKernel (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma x * (Complex.Gamma (1 - x))⁻¹ ^ (r - 1) *
    (∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
    Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - x))

theorem boundaryKernel_eq_reflection {r : ℕ} (hr : 0 < r) (b : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    boundaryKernel r b A z n x = kernel r b A z 0 n x *
      (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ (r - 1) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * x) := by
  simp only [kernel, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  symm
  calc
    _ = (Complex.Gamma x ^ r *
          (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ (r - 1)) *
        (∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
        Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - x)) := by ring
    _ = _ := by rw [gamma_power_reflection hr hx]; rfl

theorem even_boundary_kernel_fourier {r : ℕ} (hr : 0 < r) (h : ℕ) (hrh : r = 2 * h)
    (b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) * boundaryKernel r b A z n x =
      ∑ k ∈ Finset.range r, ((-1 : ℂ) ^ k * ((r - 1).choose k : ℂ)) *
        kernel r b A z ((h : ℤ) - k) n x := by
  have hp : (r - 1) + 1 = 2 * h := by omega
  have he := even_boundary_fourier (r - 1) h hp x
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne')] at he
  rw [boundaryKernel_eq_reflection hr b A z n hx]
  calc
    _ = kernel r b A z 0 n x *
        ((2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
          (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ (r - 1)) := by ring
    _ = kernel r b A z 0 n x *
        ∑ k ∈ Finset.range r, ((-1 : ℂ) ^ k * ((r - 1).choose k : ℂ)) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) - k) * x) := by rw [he]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [kernel, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
      push_cast
      ring

end ThisWork
