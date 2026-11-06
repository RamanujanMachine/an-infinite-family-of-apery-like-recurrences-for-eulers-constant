module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Power substitution on a finite ray, allowing an integrable endpoint singularity. -/

public section

namespace Neuschel

open Set MeasureTheory

/-- The real radial part of `u = w^μ`. No continuity at zero is required of
the integrand, so this applies to the fractional powers in Laplace's method. -/
theorem integral_nat_power_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : ℕ} (hμ : μ ≠ 0) (f : ℝ → E) :
    (∫ t : ℝ in 0..1, ((μ : ℝ) * t ^ (μ - 1)) • f (t ^ μ)) = ∫ u : ℝ in 0..1, f u := by
  simpa only [Function.comp_def, zero_pow hμ, one_pow] using
    (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (f := fun t : ℝ => t ^ μ) (f' := fun t => (μ : ℝ) * t ^ (μ - 1)) (g := f)
      (a := 0) (b := 1) (continuous_pow μ).continuousOn
      (fun t _ => hasDerivAt_pow μ t)
      (fun t ht => mul_nonneg (Nat.cast_nonneg μ)
        (pow_nonneg (show 0 ≤ t from by simpa using ht.1.le) _)))

theorem power_jacobian_rpow {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ (μ - 1) * (t ^ μ) ^ (((k : ℝ) + 1) / (μ : ℝ) - 1) = t ^ k := by
  rw [← Real.rpow_natCast t (μ - 1), ← Real.rpow_natCast t μ,
    ← Real.rpow_mul ht.le, ← Real.rpow_add ht, ← Real.rpow_natCast t k]
  congr 1
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hμ), Nat.cast_one, mul_sub,
    mul_div_cancel₀ _ (show (μ : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hμ)]
  ring

/-- The full weighted radial substitution, with the fractional endpoint power
and the reciprocal Jacobian made explicit. -/
theorem integral_weighted_power_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) (f : ℝ → E) :
    (∫ t : ℝ in 0..1, t ^ k • f t) =
      (μ : ℝ)⁻¹ • ∫ u : ℝ in 0..1,
        u ^ (((k : ℝ) + 1) / (μ : ℝ) - 1) • f (u ^ ((μ : ℝ)⁻¹)) := by
  have hsub := integral_nat_power_substitution hμ
    (fun u => u ^ (((k : ℝ) + 1) / (μ : ℝ) - 1) • f (u ^ ((μ : ℝ)⁻¹)))
  have heq : (μ : ℝ) • (∫ t : ℝ in 0..1, t ^ k • f t) =
      ∫ u : ℝ in 0..1, u ^ (((k : ℝ) + 1) / (μ : ℝ) - 1) • f (u ^ ((μ : ℝ)⁻¹)) := by
    rw [← intervalIntegral.integral_smul]
    refine (intervalIntegral.integral_congr_ae ?_).trans hsub
    filter_upwards with t ht
    have ht0 : 0 < t := (show t ∈ Ioc (0 : ℝ) 1 from by
      simpa only [uIoc_of_le zero_le_one] using ht).1
    simp only [Real.pow_rpow_inv_natCast ht0.le hμ, smul_smul, mul_assoc,
      power_jacobian_rpow hμ k ht0]
  simpa only [smul_smul, inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hμ), one_smul] using
    congrArg (fun u : E => (μ : ℝ)⁻¹ • u) heq

end Neuschel
