module

public import ThisWork.PowerMomentReference

/-! Moment limits for the actual defining integral vector. The common
normalizer is independent of the moment index; the coordinate change is a
diagonal power scaling. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric
open scoped Topology

noncomputable def powerMomentTransform (r n : ℕ) : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun v k := ((-(largeScale r n : ℂ)) ^ k.val)⁻¹ * v k
  map_add' := by intro v w; funext k; simp only [Pi.add_apply, mul_add]
  map_smul' := by intro c v; funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

namespace OffCutLocalData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

def offset : ℕ := D.localData.shift + D.family.firstIndex

theorem index_eq_add_offset (n : ℕ) : D.index n = n + D.offset := by
  simp only [index, offset, Nat.add_assoc]

noncomputable def localNormalizer (n : ℕ) : ℂ :=
  D.gaussianFactor n / ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (largeScale r (D.index n) : ℂ) * D.saddleKernel 0 n)

noncomputable def normalizingScalar (n : ℕ) : ℂ := D.localNormalizer (n - D.offset)

theorem eventually_localNormalizer_ne_zero (hr : 1 < r) (hA : ∀ i, 0 < A i) :
    ∀ᶠ n : ℕ in atTop, D.localNormalizer n ≠ 0 := by
  filter_upwards [D.eventually_saddleKernel_ne_zero (by omega : 0 < r) hA 0,
    ((largeScale_tendsto hr).comp D.index_tendsto).eventually (eventually_gt_atTop (0 : ℝ))] with n hnK hR
  have hroot : D.localData.quadraticRoot n ≠ 0 := Neuschel.leadingRoot_ne_zero 2
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr D.localData.speed_pos.ne') D.tangent_ne_zero) _
  have hG : Real.Gamma (1 / 2 : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have hRp := (Real.rpow_pos_of_pos hR (1 / 2 : ℝ)).ne'
  have hcf : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := inv_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  exact div_ne_zero (mul_ne_zero hroot (Complex.ofReal_ne_zero.mpr (div_ne_zero hRp hG)))
    (mul_ne_zero (mul_ne_zero hcf (Complex.ofReal_ne_zero.mpr hR.ne')) hnK)

theorem local_normalized_originalMoment_tendsto (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (k : Fin r) :
    Tendsto (fun n => D.localNormalizer n *
      powerMomentTransform r (D.index n) (branchIntegral r 0 A z j (D.index n)) k) atTop
      (𝓝 (((saddleScale r A z : ℂ) * Phase.rho θ) ^ k.val)) := by
  obtain ⟨B, hB, hlim⟩ := D.exists_normalizedGlobalMoment_tendsto hr hA hz 0 k.val
  apply hlim.congr'
  filter_upwards [D.eventually_zeroCenter_branchIntegral_eq_powerMoment (by omega : 1 < r) hA hB,
    D.eventually_saddleKernel_ne_zero (by omega : 0 < r) hA 0,
    ((largeScale_tendsto (show 1 < r by omega)).comp D.index_tendsto).eventually
      (eventually_gt_atTop (0 : ℝ))] with n hn hnK hR
  have hRc : (largeScale r (D.index n) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0 < largeScale r (D.index n) from hR).ne'
  have hcf : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := inv_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hpow : (-(largeScale r (D.index n) : ℂ)) ^ k.val ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hR.ne'))
  change _ = D.localNormalizer n *
    (((-(largeScale r (D.index n) : ℂ)) ^ k.val)⁻¹ * branchIntegral r 0 A z j (D.index n) k)
  rw [hn k]
  dsimp only [normalizedGlobalMoment, localNormalizer]
  field_simp [hcf, hRc, hnK, hpow]

theorem normalized_originalMoment_tendsto (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (k : Fin r) :
    Tendsto (fun n => D.normalizingScalar n *
      powerMomentTransform r n (branchIntegral r 0 A z j n) k) atTop
      (𝓝 (((saddleScale r A z : ℂ) * Phase.rho θ) ^ k.val)) := by
  apply (tendsto_add_atTop_iff_nat D.offset).mp
  simpa only [normalizingScalar, Nat.add_sub_cancel, D.index_eq_add_offset] using
    D.local_normalized_originalMoment_tendsto hr hA hz k

theorem eventually_normalizingScalar_ne_zero (hr : 1 < r) (hA : ∀ i, 0 < A i) :
    ∀ᶠ n : ℕ in atTop, D.normalizingScalar n ≠ 0 := by
  apply (Filter.eventually_atTop).mpr
  obtain ⟨N, hN⟩ := eventually_atTop.mp (D.eventually_localNormalizer_ne_zero hr hA)
  refine ⟨N + D.offset, fun n hn => ?_⟩
  exact hN (n - D.offset) (by omega)

end OffCutLocalData
end ThisWork
