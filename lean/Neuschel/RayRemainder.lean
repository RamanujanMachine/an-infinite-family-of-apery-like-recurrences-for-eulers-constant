module

public import Neuschel.RayMoments
public import Neuschel.LaplaceRemainder
public import Neuschel.UniformTaylor

/-! Power substitution and uniform estimates for the analytic ray remainder. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

theorem segment_weighted_radial (μ k : ℕ) (κ ρ : ℂ) (R : ℂ → ℂ) :
    segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ k * R w) 0 ρ =
      ρ ^ (k + 1) * ∫ t : ℝ in 0..1,
        t ^ k • (Complex.exp (-κ * ρ ^ μ * (t : ℂ) ^ μ) * R (t • ρ)) := by
  rw [segmentIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp [AffineMap.lineMap_apply_module', Complex.real_smul, mul_pow, pow_succ,
    mul_comm, mul_left_comm, mul_assoc]

theorem segment_weighted_power {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) (κ ρ : ℂ) (R : ℂ → ℂ) :
    segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ k * R w) 0 ρ =
      (ρ ^ (k + 1) / (μ : ℂ)) * ∫ u : ℝ in 0..1,
        Complex.exp (-(κ * ρ ^ μ) * (u : ℂ)) *
          (u ^ (((k : ℝ) + 1) / (μ : ℝ) - 1) • R ((u ^ ((μ : ℝ)⁻¹)) • ρ)) := by
  rw [segment_weighted_radial, integral_weighted_power_substitution hμ k,
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, ← div_eq_mul_inv]
  push_cast
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u hu
  have hu0 : 0 ≤ u := (show u ∈ Ioc (0 : ℝ) 1 from by
    simpa only [uIoc_of_le zero_le_one] using hu).1.le
  simp only [← Complex.ofReal_pow, Real.rpow_inv_natCast_pow hu0 hμ,
    Complex.real_smul, neg_mul, mul_left_comm, mul_assoc]

/-- A bounded analytic remainder on the straightened ray has the expected
algebraic Laplace bound, with the power substitution and Jacobian included. -/
theorem norm_segment_weighted_le {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ)
    {n η M : ℝ} (hn : 0 < n) (hη : 0 < η) (hM : 0 ≤ M) {ρ : ℂ}
    (hgap : η ≤ (ρ ^ μ).re) {R : ℂ → ℂ}
    (hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖R (t • ρ)‖ ≤ M) :
    ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k * R w) 0 ρ‖ ≤
      ‖ρ ^ (k + 1) / (μ : ℂ)‖ *
        (M * ((1 / (n * η)) ^ (((k : ℝ) + 1) / (μ : ℝ)) *
          Real.Gamma (((k : ℝ) + 1) / (μ : ℝ)))) := by
  have hs : 0 < ((k : ℝ) + 1) / (μ : ℝ) :=
    div_pos (by positivity) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hμ))
  rw [segment_weighted_power hμ k, norm_mul]
  apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  apply norm_laplace_remainder_le hs hn hη hM hgap
  intro u hu
  have hunit : u ^ ((μ : ℝ)⁻¹) ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.rpow_nonneg hu.1.le _, Real.rpow_le_one hu.1.le hu.2 (inv_nonneg.mpr (Nat.cast_nonneg μ))⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu.1.le _)]
  exact (mul_le_mul_of_nonneg_left (hR _ hunit) (Real.rpow_nonneg hu.1.le _)).trans_eq (mul_comm _ _)

/-- Compactness turns the integrated bound into a uniform algebraic error on
a family of rays inside one closed disk. -/
theorem uniform_ray_remainder {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) {r η : ℝ} (hr : 0 ≤ r) (hη : 0 < η)
    {R : ℂ → Z → ℂ} (hR : ContinuousOn (Function.uncurry R) (closedBall (0 : ℂ) r ×ˢ univ))
    {ρ : Z → ℂ} (hρ : ∀ z, ‖ρ z‖ ≤ r) (hgap : ∀ z, η ≤ (ρ z ^ μ).re) :
    ∃ C ≥ 0, ∀ n : ℝ, 0 < n → ∀ z,
      ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k * R w z) 0 (ρ z)‖ ≤
        C * n ^ (-(((k : ℝ) + 1) / (μ : ℝ))) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r |>.prod (isCompact_univ (X := Z))).exists_bound_of_continuousOn hR
  let s : ℝ := ((k : ℝ) + 1) / (μ : ℝ)
  have hs : 0 < s := div_pos (by positivity) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hμ))
  refine ⟨r ^ (k + 1) * ‖(μ : ℂ)⁻¹‖ * (max M 0 * ((1 / η) ^ s * Real.Gamma s)),
    mul_nonneg (mul_nonneg (pow_nonneg hr _) (norm_nonneg _))
      (mul_nonneg (le_max_right _ _) (mul_nonneg (Real.rpow_nonneg (one_div_nonneg.mpr hη.le) _)
        (Real.Gamma_pos_of_pos hs).le)), fun n hn z => ?_⟩
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖R (t • ρ z) z‖ ≤ max M 0 := by
    intro t ht
    have htρ : ‖t • ρ z‖ ≤ r := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, one_mul] using
        mul_le_mul ht.2 (hρ z) (norm_nonneg _) zero_le_one
    exact (show ‖R (t • ρ z) z‖ ≤ M by
      simpa only [Function.uncurry_apply_pair] using hM (t • ρ z, z)
        ⟨by simpa only [mem_closedBall, dist_zero_right] using htρ, mem_univ z⟩).trans (le_max_left M 0)
  have hB : ‖ρ z ^ (k + 1) / (μ : ℂ)‖ ≤ r ^ (k + 1) * ‖(μ : ℂ)⁻¹‖ := by
    simpa only [div_eq_mul_inv, norm_mul, norm_pow] using mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg (ρ z)) (hρ z) (k + 1)) (norm_nonneg ((μ : ℂ)⁻¹))
  have hscale : (1 / (n * η)) ^ s = (1 / η) ^ s * n ^ (-s) := by
    simp only [one_div, mul_inv_rev, Real.mul_rpow (inv_nonneg.mpr hη.le) (inv_nonneg.mpr hn.le),
      Real.inv_rpow hn.le, Real.rpow_neg hn.le]
  refine (norm_segment_weighted_le hμ k hn hη (le_max_right M 0) (hgap z) hbound).trans
    ((mul_le_mul_of_nonneg_right hB (mul_nonneg (le_max_right M 0)
      (mul_nonneg (Real.rpow_nonneg (one_div_nonneg.mpr (mul_nonneg hn.le hη.le)) _)
        (Real.Gamma_pos_of_pos hs).le))).trans_eq ?_)
  rw [hscale]
  ring

/-- The actual Taylor remainder of a compact holomorphic amplitude family has
the required uniform integrated order on the straightened rays. -/
theorem uniform_taylor_ray_remainder {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (m k : ℕ) {r D η : ℝ} (hr : 0 ≤ r) (hrD : r < D) (hη : 0 < η)
    {A : ℂ → Z → ℂ} (hA : ContinuousOn (Function.uncurry A) (ball (0 : ℂ) D ×ˢ univ))
    (hdA : ∀ z, DifferentiableOn ℂ (fun w => A w z) (ball 0 D))
    {ρ : Z → ℂ} (hρ : ∀ z, ‖ρ z‖ ≤ r) (hgap : ∀ z, η ≤ (ρ z ^ μ).re) :
    ∃ C ≥ 0, ∀ n : ℝ, 0 < n → ∀ z,
      ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k *
        (A w z - ∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z * w ^ j)) 0 (ρ z)‖ ≤
        C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) := by
  have hq := phaseQuotient_regular m isOpen_ball (mem_ball_self (hr.trans_lt hrD)) hA hdA
  obtain ⟨C, hC0, hC⟩ := uniform_ray_remainder hμ (m + k) hr hη
    (hq.1.mono (Set.prod_mono (closedBall_subset_ball hrD) Subset.rfl)) hρ hgap
  refine ⟨C, hC0, fun n hn z => ?_⟩
  have heq : (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k *
      (A w z - ∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z * w ^ j)) =
      (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ (m + k) * phaseQuotient m 0 A w z) := by
    funext w
    rw [eq_taylor_add_remainder m 0 w A z]
    simp only [sub_zero, add_sub_cancel_left, pow_add]
    ring
  simpa only [heq] using hC n hn z

end Neuschel
