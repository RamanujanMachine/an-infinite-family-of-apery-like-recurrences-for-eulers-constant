module

public import ThisWork.Argument
public import ThisWork.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Normalized kernels and moments for a fixed positive real argument `z`.
The common factor `z^n` is restored by the identities in `Normalization`.
No asymptotic property is assumed in these definitions. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter MeasureTheory
open scoped Topology

noncomputable def saddleScale [PositiveArgument] (α₁ α₂ : ℝ) : ℝ :=
  ThisWork.saddleScale α₁ α₂ PositiveArgument.value

noncomputable def kernelTwist [PositiveArgument] (j : Branch) : ℂ :=
  twist j - (Real.log PositiveArgument.value : ℂ)

/-- The Mellin–Barnes normalizedKernel with the real exponential tilt, after removing `z^n`. -/
noncomputable def normalizedKernel [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma x ^ 3 * Complex.Gamma ((α₁ : ℂ) * n - x + 1) *
    Complex.Gamma ((α₂ : ℂ) * n - x + 1) * Complex.exp (kernelTwist j * x)

/-- A fixed admissible reference contour has right edge `1/2` and heights `±1`.
For positive `αᵢ`, it lies between the left and right pole families for every `n`. -/
noncomputable def normalizedBranchIntegral [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) : Fin 3 → ℂ :=
  fun k => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((n : ℂ) - x) ^ k.val * normalizedKernel α₁ α₂ j n x)

/-- The precise norm estimate in Lemma 8, with explicit constants and an
integer threshold. The finite-dimensional norm is the sup norm on `ℂ³`. -/
def Lemma8NormEstimate [PositiveArgument] (α₁ α₂ : ℝ) : Prop :=
  ∀ j : Branch, ∃ C ≥ 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ E : ℝ,
    |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
    ‖normalizedBranchIntegral α₁ α₂ j n‖ = gammaScale α₁ α₂ n *
      Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)

/-- Both assertions of Lemma 8 for the concrete vector-valued integral sequences.
Proved by `ThisWork.lemma8` in `Neuschel/Application/Lemma8.lean`. -/
def Lemma8 [PositiveArgument] (α₁ α₂ : ℝ) : Prop :=
  Lemma8NormEstimate α₁ α₂ ∧
    LinearIndependent ℂ (fun j : Branch => normalizedBranchIntegral α₁ α₂ j)

theorem saddleScale_pos [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) : 0 < saddleScale α₁ α₂ :=
  ThisWork.saddleScale_pos h₁ h₂ PositiveArgument.positive

theorem log_saddleScale [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) :
    3 * Real.log (saddleScale α₁ α₂) = Real.log α₁ + Real.log α₂ + Real.log PositiveArgument.value :=
  ThisWork.log_saddleScale h₁ h₂ PositiveArgument.positive

end ThisWork.Analytic
