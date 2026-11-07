module

public import ThisWork.LimitingPhase
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! The Mellin–Barnes integrals and Lemma 8 at a general positive real argument. -/

@[expose] public section

namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

/-- The three limiting saddles are `saddleScale α₁ α₂ z * rho j`. -/
noncomputable def saddleScale (α₁ α₂ z : ℝ) : ℝ := (α₁ * α₂ * z) ^ (1 / 3 : ℝ)

noncomputable def gammaScale (α₁ α₂ : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (α₁ * n + 1) * Real.Gamma (α₂ * n + 1)

/-- The actual kernel, including the positive-real Meijer G factor `z^(n-x)`. -/
noncomputable def kernel (α₁ α₂ z : ℝ) (j : Branch) (n : ℕ) (x : ℂ) : ℂ :=
  Complex.Gamma x ^ 3 * Complex.Gamma ((α₁ : ℂ) * n - x + 1) *
    Complex.Gamma ((α₂ : ℂ) * n - x + 1) * Complex.exp (twist j * x) *
      Complex.exp ((Real.log z : ℂ) * ((n : ℂ) - x))

/-- Positively oriented left Hankel contour, shared by all defining integrals. -/
noncomputable def hankelIntegral (right height : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ u in Iic right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
    (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
    ∫ u in Iic right, f ((u : ℂ) + (height : ℂ) * Complex.I)

/-- Vector integral on the reference contour with right edge `1/2` and heights `±1`. -/
noncomputable def branchIntegral (α₁ α₂ z : ℝ) (j : Branch) (n : ℕ) : Fin 3 → ℂ :=
  fun k => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((n : ℂ) - x) ^ k.val * kernel α₁ α₂ z j n x)

/-- Constants and thresholds may depend on the fixed positive argument `z`. -/
def Lemma8NormEstimate (α₁ α₂ z : ℝ) : Prop :=
  ∀ j : Branch, ∃ C ≥ 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ E : ℝ,
    |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
    ‖branchIntegral α₁ α₂ z j n‖ = gammaScale α₁ α₂ n * z ^ n *
      Real.exp (-3 * saddleScale α₁ α₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)

/-- Growth and complex linear independence of the three z-dependent sequences. -/
def Lemma8 (α₁ α₂ z : ℝ) : Prop :=
  Lemma8NormEstimate α₁ α₂ z ∧
    LinearIndependent ℂ (fun j : Branch => branchIntegral α₁ α₂ z j)

theorem saddleScale_pos {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    0 < saddleScale α₁ α₂ z := Real.rpow_pos_of_pos (mul_pos (mul_pos h₁ h₂) hz) _

theorem gammaScale_pos {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (n : ℕ) :
    0 < gammaScale α₁ α₂ n := by
  apply mul_pos <;> apply Real.Gamma_pos_of_pos <;> positivity

theorem saddleScale_cube {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    saddleScale α₁ α₂ z ^ 3 = α₁ * α₂ * z := by
  simpa only [saddleScale, one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (mul_pos (mul_pos h₁ h₂) hz).le (show (3 : ℕ) ≠ 0 by decide)

theorem log_saddleScale {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    3 * Real.log (saddleScale α₁ α₂ z) = Real.log α₁ + Real.log α₂ + Real.log z := by
  have h := congrArg Real.log (saddleScale_cube h₁ h₂ hz)
  rwa [Real.log_pow, Real.log_mul (mul_pos h₁ h₂).ne' hz.ne',
    Real.log_mul h₁.ne' h₂.ne'] at h

theorem saddleScale_eq_mul {α₁ α₂ z : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hz : 0 < z) :
    saddleScale α₁ α₂ z = (α₁ * α₂) ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
  exact Real.mul_rpow (mul_pos h₁ h₂).le hz.le

@[simp] theorem saddleScale_one (α₁ α₂ : ℝ) :
    saddleScale α₁ α₂ 1 = (α₁ * α₂) ^ (1 / 3 : ℝ) := by
  simp [saddleScale]

end ThisWork
