module

public import ThisWork.NormalizerNorms
public import ThisWork.PowerMomentNorms

/-! Polynomial comparison of the original off-cut vector integrals with
their actual saddle kernels, in arbitrary rank. -/

@[expose] public section
namespace ThisWork.OffCutLocalData

open Set Filter Metric
open scoped Topology

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

theorem eventually_normalized_vector_bounds (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    ∃ M ≥ 1, ∀ᶠ n : ℕ in atTop,
      (∀ k : Fin r, ‖D.localNormalizer n *
        powerMomentTransform r (D.index n) (branchIntegral r 0 A z j (D.index n)) k‖ ≤ M) ∧
      (1 / 2 : ℝ) ≤ ‖D.localNormalizer n *
        branchIntegral r 0 A z j (D.index n) ⟨0, by omega⟩‖ := by
  let L : Fin r → ℂ := fun k => ((saddleScale r A z : ℂ) * Phase.rho θ) ^ k.val
  have hlim := tendsto_pi_nhds.mpr (fun k => D.local_normalized_originalMoment_tendsto hr hA hz k)
  have hu := hlim.norm.eventually_lt_const (lt_add_one ‖L‖)
  have hzero : Tendsto (fun n => ‖D.localNormalizer n *
      branchIntegral r 0 A z j (D.index n) ⟨0, by omega⟩‖) atTop (𝓝 1) := by
    simpa only [powerMomentTransform, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_mk,
      pow_zero, inv_one, one_mul, norm_one] using
      (D.local_normalized_originalMoment_tendsto hr hA hz ⟨0, by omega⟩).norm
  refine ⟨‖L‖ + 1, by linarith [norm_nonneg L], ?_⟩
  filter_upwards [hu, hzero.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn h0
  exact ⟨fun k => (norm_le_pi_norm _ k).trans hn.le, h0.le⟩

theorem kernel_polynomial_vector_bounds (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    ∃ L > 0, ∃ U > 0, ∀ᶠ n : ℕ in atTop,
      ‖D.saddleKernel 0 n‖ ≤ L * ‖branchIntegral r 0 A z j (D.index n)‖ ∧
      ‖branchIntegral r 0 A z j (D.index n)‖ ≤ U * (D.index n : ℝ) ^ r * ‖D.saddleKernel 0 n‖ := by
  obtain ⟨C, hC, E, hE, hscalar⟩ := D.local_normalizer_polynomial_bounds (by omega : 1 < r) hA
  obtain ⟨M, hM, hvec⟩ := D.eventually_normalized_vector_bounds hr hA hz
  refine ⟨2 * C, by positivity, M * E, by positivity, ?_⟩
  filter_upwards [hscalar, hvec, D.eventually_localNormalizer_ne_zero (by omega : 1 < r) hA,
    ((largeScale_tendsto (show 1 < r by omega)).comp D.index_tendsto).eventually
      (eventually_ge_atTop (1 : ℝ)), D.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ))]
      with n hs hv hβ hR hn
  constructor
  · have hf : ‖D.localNormalizer n * branchIntegral r 0 A z j (D.index n) ⟨0, by omega⟩‖ ≤
        ‖D.localNormalizer n‖ * ‖branchIntegral r 0 A z j (D.index n)‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (norm_nonneg _)
    have hl := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg (D.saddleKernel 0 n))
    have hm := mul_le_mul_of_nonneg_right hf (norm_nonneg (D.saddleKernel 0 n))
    have hu := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg (branchIntegral r 0 A z j (D.index n)))
    nlinarith
  · calc
      _ ≤ (D.index n : ℝ) ^ (r - 1) * M * ‖(D.localNormalizer n)⁻¹‖ :=
        norm_vector_le_of_normalized_power_moments (by omega : 0 < r) hn hR
          (by linarith) hβ _ hv.1
      _ ≤ (D.index n : ℝ) ^ (r - 1) * M * (E * (D.index n : ℝ) * ‖D.saddleKernel 0 n‖) :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = (M * E) * ((D.index n : ℝ) ^ (r - 1) * (D.index n : ℝ)) * ‖D.saddleKernel 0 n‖ := by ring
      _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]

end ThisWork.OffCutLocalData
