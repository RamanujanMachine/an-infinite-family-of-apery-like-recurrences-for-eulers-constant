module

public import ThisWork.HigherRank.OriginalMomentLimits

/-! Polynomial comparison of the actual Gaussian normalizer with the saddle
kernel. No additional asymptotic formula is assumed. -/

@[expose] public section
namespace ThisWork.HigherRank.OffCutLocalData

open Set Filter Metric
open scoped Topology

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

theorem gaussianFactor_norm {n : ℕ} (hR : 0 < largeScale r (D.index n)) :
    ‖D.gaussianFactor n‖ = ‖D.localData.quadraticRoot n‖ *
      (largeScale r (D.index n)) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) := by
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  rw [gaussianFactor, norm_mul, Complex.norm_of_nonneg (by positivity)]
  ring

theorem localNormalizer_norm {n : ℕ} (hR : 0 < largeScale r (D.index n)) :
    ‖D.localNormalizer n‖ = ‖D.localData.quadraticRoot n‖ *
      (largeScale r (D.index n)) ^ (1 / 2 : ℝ) /
        (Real.Gamma (1 / 2 : ℝ) * ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ *
          largeScale r (D.index n) * ‖D.saddleKernel 0 n‖) := by
  rw [localNormalizer, norm_div,
    norm_mul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (largeScale r (D.index n) : ℂ)) _,
    norm_mul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) _,
    Complex.norm_of_nonneg hR.le, D.gaussianFactor_norm hR]
  ring

theorem local_normalizer_polynomial_bounds (hr : 1 < r) (hA : ∀ i, 0 < A i) :
    ∃ A > 0, ∃ B > 0, ∀ᶠ n : ℕ in atTop,
      ‖D.localNormalizer n‖ * ‖D.saddleKernel 0 n‖ ≤ A ∧
      ‖(D.localNormalizer n)⁻¹‖ ≤ B * (D.index n : ℝ) * ‖D.saddleKernel 0 n‖ := by
  obtain ⟨U, hU, hroot⟩ := D.localData.uniform_quadraticRoot_bounds D.tangent_ne_zero
  have hU0 : 0 < U := by linarith
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  let c : ℝ := ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖
  have hc : 0 < c := norm_pos_iff.mpr (inv_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero))
  refine ⟨U / (Real.Gamma (1 / 2 : ℝ) * c), by positivity,
    Real.Gamma (1 / 2 : ℝ) * c * U, by positivity, ?_⟩
  filter_upwards [D.eventually_saddleKernel_ne_zero (by omega : 0 < r) hA 0,
    ((largeScale_tendsto hr).comp D.index_tendsto).eventually (eventually_ge_atTop (1 : ℝ)),
    D.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ))] with n hK hR hn
  let R := largeScale r (D.index n)
  have hR1 : 1 ≤ R := hR
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hp : 1 ≤ R ^ (1 / 2 : ℝ) := Real.one_le_rpow hR1 (by norm_num)
  have hpR : R ^ (1 / 2 : ℝ) ≤ R := Real.rpow_le_self_of_one_le hR1 (by norm_num)
  have hRn : R ≤ (D.index n : ℝ) := Real.rpow_le_self_of_one_le (by exact_mod_cast hn)
    (by linarith [div_nonneg zero_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : 1 - 1 / (r : ℝ) ≤ 1)
  have hroot0 : D.localData.quadraticRoot n ≠ 0 := Neuschel.leadingRoot_ne_zero 2
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr D.localData.speed_pos.ne') D.tangent_ne_zero) _
  have hscalar : ‖D.localNormalizer n‖ = ‖D.localData.quadraticRoot n‖ * R ^ (1 / 2 : ℝ) /
      (Real.Gamma (1 / 2 : ℝ) * c * R * ‖D.saddleKernel 0 n‖) := D.localNormalizer_norm hR0
  have hmul : ‖D.localNormalizer n‖ * ‖D.saddleKernel 0 n‖ =
      ‖D.localData.quadraticRoot n‖ * R ^ (1 / 2 : ℝ) / (Real.Gamma (1 / 2 : ℝ) * c * R) := by
    rw [hscalar]
    field_simp [norm_ne_zero_iff.mpr hK]
  have hinv : ‖(D.localNormalizer n)⁻¹‖ = Real.Gamma (1 / 2 : ℝ) * c * R *
      ‖(D.localData.quadraticRoot n)⁻¹‖ * ‖D.saddleKernel 0 n‖ / R ^ (1 / 2 : ℝ) := by
    rw [norm_inv, hscalar, norm_inv]
    field_simp [hG.ne', hc.ne', hR0.ne', (Real.rpow_pos_of_pos hR0 (1 / 2 : ℝ)).ne',
      norm_ne_zero_iff.mpr hK, norm_ne_zero_iff.mpr hroot0]
  constructor
  · rw [hmul]
    calc
      _ ≤ U * R / (Real.Gamma (1 / 2 : ℝ) * c * R) := div_le_div_of_nonneg_right
        (mul_le_mul (hroot n).1 hpR (Real.rpow_nonneg hR0.le _) hU0.le) (by positivity)
      _ = _ := by field_simp [hG.ne', hc.ne', hR0.ne']
  · rw [hinv]
    calc
      _ ≤ Real.Gamma (1 / 2 : ℝ) * c * R * ‖(D.localData.quadraticRoot n)⁻¹‖ * ‖D.saddleKernel 0 n‖ :=
        div_le_self (by positivity) hp
      _ ≤ Real.Gamma (1 / 2 : ℝ) * c * (D.index n : ℝ) * U * ‖D.saddleKernel 0 n‖ := by
        gcongr
        exact (hroot n).2
      _ = _ := by ring

end ThisWork.HigherRank.OffCutLocalData
