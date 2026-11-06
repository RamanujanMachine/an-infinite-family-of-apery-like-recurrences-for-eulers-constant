module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Uniform exponential tail estimates

This is the global remainder estimate in part (iv) of the proof of
Neuschel's Theorem 3.1. A measure-space formulation allows the contour
parameterization and its velocity to be supplied later.
-/

public section

namespace Neuschel

open MeasureTheory Filter

/-- A positive gap in the real part of the phase gives an exponential bound
relative to an already integrable base parameter. -/
theorem exp_weight_le {T N ε : ℝ} {w q : ℂ} (hT : N ≤ T) (hw : ε ≤ w.re) :
    ‖Complex.exp (-(T : ℂ) * w) * q‖ ≤
      Real.exp (-(T - N) * ε) * (Real.exp (-N * w.re) * ‖q‖) := by
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  rw [← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg q)
  nlinarith [mul_nonneg (sub_nonneg.mpr hT) (sub_nonneg.mpr hw)]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Absolute integrability at the base parameter propagates to every larger
real parameter when the phase has a lower bound. -/
theorem integrable_exp_weight {T N ε : ℝ} {p q : X → ℂ}
    (hT : N ≤ T) (hgap : ∀ᵐ x ∂μ, ε ≤ (p x).re)
    (hbase : Integrable (fun x => Real.exp (-N * (p x).re) * ‖q x‖) μ)
    (hmeas : AEStronglyMeasurable (fun x => Complex.exp (-(T : ℂ) * p x) * q x) μ) :
    Integrable (fun x => Complex.exp (-(T : ℂ) * p x) * q x) μ :=
  (hbase.const_mul (Real.exp (-(T - N) * ε))).mono' hmeas
    (hgap.mono (fun _ hx => exp_weight_le hT hx))

/-- The quantitative global remainder estimate underlying Theorem 3.1(iv).
The phase here has already been centered by subtracting its saddle value. -/
theorem norm_integral_exp_weight_le {T N ε : ℝ} {p q : X → ℂ}
    (hT : N ≤ T) (hgap : ∀ᵐ x ∂μ, ε ≤ (p x).re)
    (hbase : Integrable (fun x => Real.exp (-N * (p x).re) * ‖q x‖) μ) :
    ‖∫ x, Complex.exp (-(T : ℂ) * p x) * q x ∂μ‖ ≤
      Real.exp (-(T - N) * ε) * ∫ x, Real.exp (-N * (p x).re) * ‖q x‖ ∂μ := by
  have h := norm_integral_le_of_norm_le (hbase.const_mul (Real.exp (-(T - N) * ε)))
    (hgap.mono (fun _ hx => exp_weight_le hT hx))
  simpa only [integral_const_mul] using h

/-- A parameter-independent phase gap and base-integral bound give a uniform
exponential tail estimate. The Laplace parameter may be any real `T ≥ N`.

For contour integrals, use the restricted parameter measure on the tail and
include the contour velocity in `q`. Positivity of `ε` makes the displayed
bound decay exponentially; the inequality itself holds for every real `ε`.
-/
theorem uniform_exp_tail_bound {Z : Type*} {T N ε M : ℝ} {p q : X → Z → ℂ}
    (hT : N ≤ T)
    (hgap : ∀ z, ∀ᵐ x ∂μ, ε ≤ (p x z).re)
    (hbase : ∀ z, Integrable (fun x => Real.exp (-N * (p x z).re) * ‖q x z‖) μ)
    (hmass : ∀ z, (∫ x, Real.exp (-N * (p x z).re) * ‖q x z‖ ∂μ) ≤ M)
    (hmeas : ∀ z, AEStronglyMeasurable
      (fun x => Complex.exp (-(T : ℂ) * p x z) * q x z) μ) :
    (∀ z, Integrable (fun x => Complex.exp (-(T : ℂ) * p x z) * q x z) μ) ∧
      ∀ z, ‖∫ x, Complex.exp (-(T : ℂ) * p x z) * q x z ∂μ‖ ≤
        Real.exp (-(T - N) * ε) * M :=
  ⟨(fun z => integrable_exp_weight hT (hgap z) (hbase z) (hmeas z)),
    (fun z => (norm_integral_exp_weight_le hT (hgap z) (hbase z)).trans
      (mul_le_mul_of_nonneg_left (hmass z) (Real.exp_nonneg _)))⟩

end Neuschel
