module

public import Neuschel.RootBranch
public import Neuschel.PowerSubstitution
public import Neuschel.LaplaceMoment
public import Neuschel.ContourIntegral

/-! Monomial Laplace moments on the straightened saddle-coordinate ray. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

theorem segment_monomial_radial (μ k : ℕ) (κ ρ : ℂ) :
    segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ k) 0 ρ =
      ρ ^ (k + 1) * ∫ t : ℝ in 0..1,
        t ^ k • Complex.exp (-κ * ρ ^ μ * (t : ℂ) ^ μ) := by
  rw [segmentIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp [AffineMap.lineMap_apply_module', Complex.real_smul, mul_pow, pow_succ,
    mul_comm, mul_assoc]

theorem segment_monomial_moment {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) (κ ρ : ℂ) :
    segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ k) 0 ρ =
      (ρ ^ (k + 1) / (μ : ℂ)) * ∫ u : ℝ in 0..1,
        momentKernel (((k : ℝ) + 1) / (μ : ℝ)) (κ * ρ ^ μ) u := by
  rw [segment_monomial_radial, integral_weighted_power_substitution hμ k]
  rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, ← div_eq_mul_inv]
  push_cast
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u hu
  have hu0 : 0 ≤ u := (show u ∈ Ioc (0 : ℝ) 1 from by
    simpa only [uIoc_of_le zero_le_one] using hu).1.le
  simp only [← Complex.ofReal_pow, Real.rpow_inv_natCast_pow hu0 hμ,
    Complex.real_smul, momentKernel, neg_mul]

/-- Each straightened Taylor monomial has its Gamma asymptotic, uniformly in
the compact family of phase endpoints, with exponentially small error. -/
theorem uniform_segment_monomial {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) {η : ℝ} (hη : 0 < η)
    {α : Z → ℂ} (hα : Continuous α) (hgap : ∀ z, η ≤ (α z).re) :
    ∃ C ≥ 0, ∀ n : ℝ, 1 ≤ n → ∀ z,
      ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k) 0 (normalizedRoot μ (α z)) -
        (μ : ℂ)⁻¹ * ((Real.Gamma (((k : ℝ) + 1) / (μ : ℝ)) /
          n ^ (((k : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)‖ ≤ C * Real.exp (-(n - 1) * η) := by
  have hs : 0 < ((k : ℝ) + 1) / (μ : ℝ) :=
    div_pos (by positivity) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hμ))
  obtain ⟨C, hC0, hC⟩ := uniform_scaled_incomplete_laplace_moment hs hη hα hgap
  refine ⟨‖(μ : ℂ)⁻¹‖ * C, mul_nonneg (norm_nonneg _) hC0, fun n hn z => ?_⟩
  have hα0 : α z ≠ 0 := Complex.slitPlane_ne_zero (Or.inl (hη.trans_le (hgap z)))
  have heq : segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k) 0 (normalizedRoot μ (α z)) =
      (μ : ℂ)⁻¹ * (α z ^ ((((k : ℝ) + 1) / (μ : ℝ) : ℝ) : ℂ) *
        ∫ u : ℝ in 0..1, momentKernel (((k : ℝ) + 1) / (μ : ℝ)) ((n : ℂ) * α z) u) := by
    rw [segment_monomial_moment hμ k, normalizedRoot_pow hμ hα0,
      normalizedRoot_nat_power μ k hα0, div_eq_mul_inv]
    ring
  rw [heq, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hC n hn z) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

end Neuschel
