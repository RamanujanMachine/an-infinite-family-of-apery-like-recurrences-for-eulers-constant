module

public import Neuschel.UniformLaplace

/-! Exponential prefactor and integer-parameter form of uniform expansions. -/

public section

namespace Neuschel

open Set Filter MeasureTheory
open scoped Topology

theorem integral_centered_exp {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (n : ℝ) (p q : X → ℂ) (a : ℂ) :
    (∫ x, Complex.exp (-(n : ℂ) * (p x - a)) * q x ∂ν) =
      Complex.exp ((n : ℂ) * a) * ∫ x, Complex.exp (-(n : ℂ) * p x) * q x ∂ν := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have heq : -(n : ℂ) * (p x - a) = (n : ℂ) * a + -(n : ℂ) * p x := by ring
  rw [heq, Complex.exp_add, mul_assoc]

/-- Restoring the saddle exponential is an exact identity for the residual,
including before the asymptotic range. -/
theorem uncentered_residual {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (n : ℝ) (p q : X → ℂ) (a S : ℂ) :
    (∫ x, Complex.exp (-(n : ℂ) * p x) * q x ∂ν) =
      Complex.exp (-(n : ℂ) * a) *
        (S + ((∫ x, Complex.exp (-(n : ℂ) * (p x - a)) * q x ∂ν) - S)) := by
  rw [← add_sub_assoc, add_sub_cancel_left, integral_centered_exp, ← mul_assoc, ← Complex.exp_add]
  simp

/-- Coefficients of the uniform contour expansion in the paper's convention.
Here `λ = k + 1`; the remainder is uniform in `z` for every truncation order. -/
structure UniformLaplaceExpansion {Z : Type*} [TopologicalSpace Z] (μ k : ℕ)
    (P q : ℂ → Z → ℂ) (a v : ℂ) (b c : ℕ → Z → ℂ) (γ velocity : ℝ → ℂ) (N : ℝ) where
  absolute_convergence : ∀ (n : ℕ), N ≤ (n : ℝ) → ∀ z, IntegrableOn
    (fun s => Complex.exp (-(n : ℂ) * P (γ s) z) * (velocity s * q (γ s) z)) (Ioo 0 1)
  coefficient : ℕ → Z → ℂ
  coefficient_continuous : ∀ j, Continuous (coefficient j)
  coefficient_zero : ∀ z, coefficient 0 z =
    c 0 z / ((μ : ℂ) * leadingRoot μ v (b 0 z) ^ (k + 1))
  coefficient_one : ∀ z, coefficient 1 z =
    (c 1 z - ((k : ℂ) + 2) * b 1 z * c 0 z / ((μ : ℂ) * b 0 z)) /
      ((μ : ℂ) * leadingRoot μ v (b 0 z) ^ (k + 2))
  remainder : ℕ → ℕ → Z → ℂ
  expansion : ∀ (m n : ℕ) z,
    (∫ s in Ioo (0 : ℝ) 1, Complex.exp (-(n : ℂ) * P (γ s) z) * (velocity s * q (γ s) z)) =
      Complex.exp (-(n : ℂ) * P a z) *
        ((∑ j ∈ Finset.range m, coefficient j z *
          ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
            (n : ℝ) ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)) + remainder m n z)
  remainder_bound : ∀ m, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ z,
    ‖remainder m n z‖ ≤ C * (n : ℝ) ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ)))

/-- The second coefficient in exactly the algebraic convention used in the paper. -/
theorem UniformLaplaceExpansion.coefficient_one_paper_form {Z : Type*} [TopologicalSpace Z]
    {μ k : ℕ} {P q : ℂ → Z → ℂ} {a v : ℂ} {b c : ℕ → Z → ℂ}
    {γ velocity : ℝ → ℂ} {N : ℝ}
    (E : UniformLaplaceExpansion μ k P q a v b c γ velocity N) (z : Z) :
    E.coefficient 1 z =
      (c 1 z / (μ : ℂ) - ((k : ℂ) + 2) * b 1 z * c 0 z / ((μ : ℂ) ^ 2 * b 0 z)) /
        leadingRoot μ v (b 0 z) ^ (k + 2) := by
  rw [E.coefficient_one z]
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  ring

end Neuschel
