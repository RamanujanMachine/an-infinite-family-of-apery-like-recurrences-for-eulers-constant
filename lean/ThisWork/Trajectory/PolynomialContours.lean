module

public import ThisWork.HankelLinearity
public import ThisWork.HankelDeformation

/-! Polynomial weights preserve the established Hankel convergence and deformation.
These results are independent of the degree of the polynomial. They do not assert
bounds uniform in a growing degree. -/

@[expose] public section

namespace ThisWork.Analytic

open Set MeasureTheory Polynomial

/-- Absolute convergence for any polynomial in the original moment variable. -/
theorem polynomial_moment_hankel_integrable [PositiveArgument] {A₁ A₂ r h : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (j : Branch) (n : ℕ)
    (hr₀ : 0 < r) (hr : r < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h)
    (P : ℂ[X]) :
    HankelIntegrable r h (fun x => P.eval ((n : ℂ) - x) * normalizedKernel A₁ A₂ j n x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
      simpa only [eval_add, add_mul] using hp.add hq
  | monomial k a =>
      simpa only [eval_monomial, mul_assoc] using
        (show HankelIntegrable r h (fun x => ((n : ℂ) - x) ^ k * normalizedKernel A₁ A₂ j n x)
          from weighted_hankel_absolutely_convergent h₁ h₂ j n k hr₀ hr hh).const_mul a

/-- Absolute convergence for a polynomial in the contour coordinate itself. -/
theorem polynomial_hankel_integrable [PositiveArgument] {A₁ A₂ r h : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (j : Branch) (n : ℕ)
    (hr₀ : 0 < r) (hr : r < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h)
    (P : ℂ[X]) :
    HankelIntegrable r h (fun x => P.eval x * normalizedKernel A₁ A₂ j n x) := by
  have hP := polynomial_moment_hankel_integrable h₁ h₂ j n hr₀ hr hh
    (P.comp (C (n : ℂ) - X))
  simp_rw [eval_comp, eval_sub, eval_C, eval_X, sub_sub_cancel] at hP
  exact hP

/-- The polynomial moment integrals are invariant under admissible polygon changes. -/
theorem polynomial_moment_hankel_eq [PositiveArgument] {A₁ A₂ r s h t : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (j : Branch) (n : ℕ)
    (hr₀ : 0 < r) (hs₀ : 0 < s)
    (hr : r < min (A₁ * n + 1) (A₂ * n + 1))
    (hs : s < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (P : ℂ[X]) :
    hankelIntegral r h (fun x => P.eval ((n : ℂ) - x) * normalizedKernel A₁ A₂ j n x) =
      hankelIntegral s t (fun x => P.eval ((n : ℂ) - x) * normalizedKernel A₁ A₂ j n x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
      simp only [eval_add, add_mul]
      rw [hankelIntegral_add
        (polynomial_moment_hankel_integrable h₁ h₂ j n hr₀ hr hh P)
        (polynomial_moment_hankel_integrable h₁ h₂ j n hr₀ hr hh Q),
        hankelIntegral_add
        (polynomial_moment_hankel_integrable h₁ h₂ j n hs₀ hs ht P)
        (polynomial_moment_hankel_integrable h₁ h₂ j n hs₀ hs ht Q), hp, hq]
  | monomial k a =>
      simp only [eval_monomial, mul_assoc, hankelIntegral_const_mul]
      exact congrArg (a * ·)
        ((weighted_hankel_height_eq h₁ h₂ j n k hr₀ hr hh ht).trans
          (weighted_hankel_right_eq h₁ h₂ j n k hr₀ hs₀ hr hs ht))

theorem polynomial_hankel_eq [PositiveArgument] {A₁ A₂ r s h t : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (j : Branch) (n : ℕ)
    (hr₀ : 0 < r) (hs₀ : 0 < s)
    (hr : r < min (A₁ * n + 1) (A₂ * n + 1))
    (hs : s < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (P : ℂ[X]) :
    hankelIntegral r h (fun x => P.eval x * normalizedKernel A₁ A₂ j n x) =
      hankelIntegral s t (fun x => P.eval x * normalizedKernel A₁ A₂ j n x) := by
  have hP := polynomial_moment_hankel_eq h₁ h₂ j n hr₀ hs₀ hr hs hh ht
    (P.comp (C (n : ℂ) - X))
  simp_rw [eval_comp, eval_sub, eval_C, eval_X, sub_sub_cancel] at hP
  exact hP

end ThisWork.Analytic
