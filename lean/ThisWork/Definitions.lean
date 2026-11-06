module

public import ThisWork.LimitingPhase
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Concrete integral definitions and the statement of Lemma 8.
No asymptotic property is assumed in these definitions. -/

@[expose] public section

namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

noncomputable def saddleScale (α₁ α₂ : ℝ) : ℝ := (α₁ * α₂) ^ (1 / 3 : ℝ)

noncomputable def gammaScale (α₁ α₂ : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (α₁ * n + 1) * Real.Gamma (α₂ * n + 1)

/-- The original Mellin–Barnes kernel, before logarithms or saddle normalization. -/
noncomputable def kernel (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma x ^ 3 * Complex.Gamma ((α₁ : ℂ) * n - x + 1) *
    Complex.Gamma ((α₂ : ℂ) * n - x + 1) * Complex.exp (twist j * x)

/-- A positively oriented left Hankel loop with a vertical right edge and
horizontal infinite tails. All integrals retain their actual complex integrands. -/
noncomputable def hankelIntegral (right height : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ u in Iic right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
    (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
    ∫ u in Iic right, f ((u : ℂ) + (height : ℂ) * Complex.I)

/-- A fixed admissible reference contour has right edge `1/2` and heights `±1`.
For positive `αᵢ`, it lies between the left and right pole families for every `n`. -/
noncomputable def branchIntegral (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) : Fin 3 → ℂ :=
  fun k => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((n : ℂ) - x) ^ k.val * kernel α₁ α₂ j n x)

/-- The precise norm estimate in Lemma 8, with explicit constants and an
integer threshold. The finite-dimensional norm is the sup norm on `ℂ³`. -/
def Lemma8NormEstimate (α₁ α₂ : ℝ) : Prop :=
  ∀ j : Branch, ∃ C ≥ 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ E : ℝ,
    |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
    ‖branchIntegral α₁ α₂ j n‖ = gammaScale α₁ α₂ n *
      Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)

/-- Both assertions of Lemma 8 for the concrete vector-valued integral sequences.
Proved by `ThisWork.lemma8` in `Neuschel/Application/Lemma8.lean`. -/
def Lemma8 (α₁ α₂ : ℝ) : Prop :=
  Lemma8NormEstimate α₁ α₂ ∧
    LinearIndependent ℂ (fun j : Branch => branchIntegral α₁ α₂ j)

theorem saddleScale_pos {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) :
    0 < saddleScale α₁ α₂ := Real.rpow_pos_of_pos (mul_pos h₁ h₂) _

theorem gammaScale_pos {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (n : ℕ) :
    0 < gammaScale α₁ α₂ n := by
  apply mul_pos <;> apply Real.Gamma_pos_of_pos <;> positivity

theorem saddleScale_cube {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) :
    saddleScale α₁ α₂ ^ 3 = α₁ * α₂ := by
  simpa only [saddleScale, one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (mul_pos h₁ h₂).le (show (3 : ℕ) ≠ 0 by decide)

end ThisWork
