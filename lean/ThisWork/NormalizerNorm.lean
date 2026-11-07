module

public import ThisWork.Argument
public import ThisWork.OriginalMomentLimits

/-! Polynomial bounds for the nonzero saddle normalizers. -/

public section

namespace ThisWork.Analytic.CompactSaddleFamily.LocalSaddleData


open Set Filter Metric
open scoped Topology OnePoint

theorem normalizingScalar_norm [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) {n : ℕ} (hn : 0 < n) :
    ‖D.normalizingScalar n‖ =
      ‖D.quadraticRoot (n - D.offset)‖ * (largeScale n ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ)) /
        (‖D.rawKernel n‖ * ‖cauchyFactor‖ * largeScale n) := by
  have hR := largeScale_pos hn
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  rw [normalizingScalar, norm_div]
  simp only [norm_mul, norm_branchOrientation, one_mul,
    Complex.norm_of_nonneg (div_pos (Real.rpow_pos_of_pos hR _) hG).le,
    Complex.norm_of_nonneg hR.le]

theorem normalizingScalar_norm_mul_kernel [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) {n : ℕ} (hn : 0 < n) (hK : D.rawKernel n ≠ 0) :
    ‖D.normalizingScalar n‖ * ‖D.rawKernel n‖ =
      ‖D.quadraticRoot (n - D.offset)‖ * largeScale n ^ (1 / 2 : ℝ) /
        (Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * largeScale n) := by
  rw [D.normalizingScalar_norm hn]
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hR := largeScale_pos hn
  have hcn : ‖cauchyFactor‖ ≠ 0 := norm_ne_zero_iff.mpr cauchyFactor_ne_zero
  field_simp [norm_ne_zero_iff.mpr hK, hG.ne', hR.ne', hcn]

theorem inv_normalizingScalar_norm [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) {n : ℕ} (hn : 0 < n) (hK : D.rawKernel n ≠ 0) :
    ‖(D.normalizingScalar n)⁻¹‖ =
      Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * largeScale n *
        ‖(D.quadraticRoot (n - D.offset))⁻¹‖ * ‖D.rawKernel n‖ /
          largeScale n ^ (1 / 2 : ℝ) := by
  simp only [norm_inv]
  rw [D.normalizingScalar_norm hn]
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hR := largeScale_pos hn
  have hp := Real.rpow_pos_of_pos hR (1 / 2 : ℝ)
  have hcn : ‖cauchyFactor‖ ≠ 0 := norm_ne_zero_iff.mpr cauchyFactor_ne_zero
  have hroot : ‖D.quadraticRoot (n - D.offset)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Neuschel.leadingRoot_ne_zero 2 D.velocity_ne_zero _)
  field_simp [norm_ne_zero_iff.mpr hK, hG.ne', hR.ne', hp.ne', hcn, hroot]

theorem normalizingScalar_polynomial_bounds [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ A > 0, ∃ B > 0, ∀ᶠ n : ℕ in atTop,
      ‖D.normalizingScalar n‖ * ‖D.rawKernel n‖ ≤ A ∧
      ‖(D.normalizingScalar n)⁻¹‖ ≤ B * (n : ℝ) * ‖D.rawKernel n‖ := by
  obtain ⟨B, hB, hb⟩ := D.uniform_quadraticRoot_bounds h₁ h₂
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hc : 0 < ‖cauchyFactor‖ := norm_pos_iff.mpr cauchyFactor_ne_zero
  refine ⟨B / (Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖), by positivity,
    Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * B, by positivity, ?_⟩
  filter_upwards [D.eventually_rawKernel_ne_zero h₁ h₂, eventually_ge_atTop (1 : ℕ),
    largeScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hK hn hR
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hR0 : 0 < largeScale n := by linarith
  have hp : 1 ≤ largeScale n ^ (1 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hpR : largeScale n ^ (1 / 2 : ℝ) ≤ largeScale n := Real.rpow_le_self_of_one_le hR (by norm_num)
  have hRn : largeScale n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le hn1 (by norm_num : (2 / 3 : ℝ) ≤ 1)
  constructor
  · rw [D.normalizingScalar_norm_mul_kernel hn0 hK]
    calc
      _ ≤ B * largeScale n / (Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * largeScale n) :=
        div_le_div_of_nonneg_right (mul_le_mul (hb (n - D.offset)).1 hpR (by positivity) (by positivity)) (by positivity)
      _ = _ := by field_simp [hG.ne', hc.ne', hR0.ne']
  · rw [D.inv_normalizingScalar_norm hn0 hK]
    calc
      _ ≤ Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * largeScale n *
          ‖(D.quadraticRoot (n - D.offset))⁻¹‖ * ‖D.rawKernel n‖ := div_le_self (by positivity) hp
      _ ≤ Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * largeScale n * B * ‖D.rawKernel n‖ := by
        gcongr
        exact (hb (n - D.offset)).2
      _ ≤ Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * (n : ℝ) * B * ‖D.rawKernel n‖ := by gcongr
      _ = _ := by ring

/-- The Gaussian amplitude differs from the saddle normalizedKernel only by polynomial factors. -/
theorem gaussianAmplitude_kernel_bounds [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ A > 0, ∃ B > 0, ∀ᶠ n : ℕ in atTop,
      ‖D.rawKernel n‖ ≤ A * ‖D.gaussianAmplitude n‖ ∧
      ‖D.gaussianAmplitude n‖ ≤ B * (n : ℝ) * ‖D.rawKernel n‖ := by
  obtain ⟨A, hA, B, hB, hb⟩ := D.normalizingScalar_polynomial_bounds h₁ h₂
  refine ⟨A, hA, B, hB, ?_⟩
  filter_upwards [hb, D.eventually_normalizingScalar_ne_zero h₁ h₂] with n hn hN
  refine ⟨?_, hn.2⟩
  simpa only [gaussianAmplitude, norm_inv, div_eq_mul_inv] using
    (le_div_iff₀ (norm_pos_iff.mpr hN)).mpr (by simpa only [mul_comm] using hn.1)

end ThisWork.Analytic.CompactSaddleFamily.LocalSaddleData
