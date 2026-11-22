module

public import ThisWork.HigherRank.OriginalMomentLimits

/-! Polynomial conditioning of the arbitrary-rank power-moment coordinates. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem norm_powerMomentTransform_le {r n : ℕ} (hR : 1 ≤ largeScale r n) (v : Fin r → ℂ) :
    ‖powerMomentTransform r n v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro k
  change ‖((-(largeScale r n : ℂ)) ^ k.val)⁻¹ * v k‖ ≤ ‖v‖
  rw [norm_mul, norm_inv, norm_pow, norm_neg, Complex.norm_of_nonneg (by linarith : 0 ≤ largeScale r n)]
  have hp : 1 ≤ largeScale r n ^ k.val := one_le_pow₀ hR
  have hi : (largeScale r n ^ k.val)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  exact (mul_le_of_le_one_left (norm_nonneg _) hi).trans (norm_le_pi_norm v k)

theorem norm_vector_le_of_normalized_power_moments {r n : ℕ} (hr : 0 < r) (hn : 1 ≤ n)
    (hR : 1 ≤ largeScale r n) {M : ℝ} (hM : 0 ≤ M) {a : ℂ} (ha : a ≠ 0)
    (v : Fin r → ℂ) (hv : ∀ k, ‖a * powerMomentTransform r n v k‖ ≤ M) :
    ‖v‖ ≤ (n : ℝ) ^ (r - 1) * M * ‖a⁻¹‖ := by
  have hR0 : 0 < largeScale r n := zero_lt_one.trans_le hR
  have hRn : largeScale r n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le
    (by exact_mod_cast hn) (by linarith [div_nonneg zero_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : 1 - 1 / (r : ℝ) ≤ 1)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  have hp0 : (-(largeScale r n : ℂ)) ^ k.val ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hR0.ne'))
  have hid : v k = a⁻¹ * (-(largeScale r n : ℂ)) ^ k.val * (a * powerMomentTransform r n v k) := by
    change _ = a⁻¹ * (-(largeScale r n : ℂ)) ^ k.val *
      (a * (((-(largeScale r n : ℂ)) ^ k.val)⁻¹ * v k))
    field_simp [ha, hp0]
  have hpow : largeScale r n ^ k.val ≤ (n : ℝ) ^ (r - 1) :=
    (pow_le_pow_right₀ hR (by omega : k.val ≤ r - 1)).trans
      (pow_le_pow_left₀ hR0.le hRn (r - 1))
  rw [hid, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_of_nonneg hR0.le]
  calc
    _ ≤ (‖a⁻¹‖ * (n : ℝ) ^ (r - 1)) * M := mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) (hv k) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ThisWork.HigherRank
