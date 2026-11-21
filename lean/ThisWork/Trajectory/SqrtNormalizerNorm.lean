module
public import ThisWork.Trajectory.SqrtOriginalMoments
/-! Polynomial comparison between the canonical Gaussian amplitude and kernel. -/
public section
namespace ThisWork.Trajectory.CanonicalSaddleData
open Set Filter Metric Analytic
open scoped Topology OnePoint
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : CanonicalSaddleData m d A₁ A₂ z)
theorem normalizingScalar_norm  {n : ℕ} (hn : 0 < F.index n) :
    ‖F.normalizingScalar n‖ =
      ‖F.data.quadraticRoot n‖ * (sqrtScale (F.index n) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ)) /
        (‖F.saddleKernel n‖ * ‖cauchyFactor‖ * sqrtScale (F.index n)) := by
  have hR := sqrtScale_pos hn
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  rw [normalizingScalar, gaussianNormalizer, norm_div]
  simp only [norm_mul, 
    Complex.norm_of_nonneg (div_pos (Real.rpow_pos_of_pos hR _) hG).le,
    Complex.norm_of_nonneg hR.le]

theorem normalizingScalar_norm_mul_kernel  {n : ℕ} (hn : 0 < F.index n) (hK : F.saddleKernel n ≠ 0) :
    ‖F.normalizingScalar n‖ * ‖F.saddleKernel n‖ =
      ‖F.data.quadraticRoot n‖ * sqrtScale (F.index n) ^ (1 / 2 : ℝ) /
        (Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * sqrtScale (F.index n)) := by
  rw [F.normalizingScalar_norm hn]
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hR := sqrtScale_pos hn
  have hcn : ‖cauchyFactor‖ ≠ 0 := norm_ne_zero_iff.mpr cauchyFactor_ne_zero
  field_simp [norm_ne_zero_iff.mpr hK, hG.ne', hR.ne', hcn]

theorem inv_normalizingScalar_norm  {n : ℕ} (hn : 0 < F.index n) (hK : F.saddleKernel n ≠ 0) :
    ‖(F.normalizingScalar n)⁻¹‖ =
      Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * sqrtScale (F.index n) *
        ‖(F.data.quadraticRoot n)⁻¹‖ * ‖F.saddleKernel n‖ /
          sqrtScale (F.index n) ^ (1 / 2 : ℝ) := by
  simp only [norm_inv]
  rw [F.normalizingScalar_norm hn]
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hR := sqrtScale_pos hn
  have hp := Real.rpow_pos_of_pos hR (1 / 2 : ℝ)
  have hcn : ‖cauchyFactor‖ ≠ 0 := norm_ne_zero_iff.mpr cauchyFactor_ne_zero
  have hroot : ‖F.data.quadraticRoot n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Neuschel.leadingRoot_ne_zero 2 F.data.velocity_ne_zero _)
  field_simp [norm_ne_zero_iff.mpr hK, hG.ne', hR.ne', hp.ne', hcn, hroot]

theorem normalizingScalar_polynomial_bounds  :
    ∃ A > 0, ∃ B > 0, ∀ᶠ n : ℕ in atTop,
      ‖F.normalizingScalar n‖ * ‖F.saddleKernel n‖ ≤ A ∧
      ‖(F.normalizingScalar n)⁻¹‖ ≤ B * (F.index n : ℝ) * ‖F.saddleKernel n‖ := by
  obtain ⟨B, hB, hb⟩ := F.data.uniform_quadraticRoot_bounds
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hc : 0 < ‖cauchyFactor‖ := norm_pos_iff.mpr cauchyFactor_ne_zero
  refine ⟨B / (Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖), by positivity,
    Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * B, by positivity, ?_⟩
  filter_upwards [F.eventually_saddleKernel_ne_zero, F.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ)),
    (sqrtScale_tendsto.comp F.index_tendsto).eventually (eventually_ge_atTop (1 : ℝ))] with n hK hn hR
  change 1 ≤ sqrtScale (F.index n) at hR
  have hn0 : 0 < F.index n := by omega
  have hn1 : 1 ≤ (F.index n : ℝ) := by exact_mod_cast hn
  have hR0 : 0 < sqrtScale (F.index n) := by linarith
  have hp : 1 ≤ sqrtScale (F.index n) ^ (1 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hpR : sqrtScale (F.index n) ^ (1 / 2 : ℝ) ≤ sqrtScale (F.index n) := Real.rpow_le_self_of_one_le hR (by norm_num)
  have hRn : sqrtScale (F.index n) ≤ (F.index n : ℝ) := sqrtScale_le_nat hn
  constructor
  · rw [F.normalizingScalar_norm_mul_kernel hn0 hK]
    calc
      _ ≤ B * sqrtScale (F.index n) / (Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * sqrtScale (F.index n)) :=
        div_le_div_of_nonneg_right (mul_le_mul (hb n).1 hpR (by positivity) (by positivity)) (by positivity)
      _ = _ := by field_simp [hG.ne', hc.ne', hR0.ne']
  · rw [F.inv_normalizingScalar_norm hn0 hK]
    calc
      _ ≤ Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * sqrtScale (F.index n) *
          ‖(F.data.quadraticRoot n)⁻¹‖ * ‖F.saddleKernel n‖ := div_le_self (by positivity) hp
      _ ≤ Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * sqrtScale (F.index n) * B * ‖F.saddleKernel n‖ := by
        gcongr
        exact (hb n).2
      _ ≤ Real.Gamma (1 / 2 : ℝ) * ‖cauchyFactor‖ * (F.index n : ℝ) * B * ‖F.saddleKernel n‖ := by gcongr
      _ = _ := by ring


end ThisWork.Trajectory.CanonicalSaddleData
