module

public import ThisWork.Definitions
public import Mathlib.Algebra.BigOperators.Fin

/-! Equal-lower-slope Mellin–Barnes kernels in arbitrary rank.
The integer label records the factor `exp(2πi*j*x)`; it does not assert that a
particular principal-log saddle or contour is admissible. -/

@[expose] public section
namespace ThisWork.HigherRank

noncomputable def kernel (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma x ^ r *
    (∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * j * x) *
    Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - x))

noncomputable def branchIntegral (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (n : ℕ) : Fin r → ℂ := fun k =>
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((b : ℂ) * n - x) ^ k.val * kernel r b A z j n x)

noncomputable def gammaScale (r : ℕ) (A : Fin (r - 1) → ℝ) (n : ℕ) : ℝ :=
  ∏ i, Real.Gamma (A i * n + 1)

noncomputable def commonScale (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (n : ℕ) : ℝ := gammaScale r A n * z ^ (b * n)

noncomputable def saddleScale (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) : ℝ :=
  ((∏ i, A i) * z) ^ (1 / (r : ℝ))

end ThisWork.HigherRank
