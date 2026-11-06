module

public import ThisWork.NormalizerNorm
public import ThisWork.VectorMomentBounds
public import ThisWork.VectorAsymptotics

/-! Polynomial comparison of the original vector norm with the actual saddle kernel. -/

public section

namespace ThisWork.CompactSaddleFamily.LocalSaddleData

open Set Filter Metric
open scoped Topology OnePoint

theorem eventually_normalized_vector_bounds {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ M ≥ 1, ∀ᶠ n : ℕ in atTop,
      (∀ k : Fin 3, ‖D.normalizingScalar n *
        momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) k‖ ≤ M) ∧
      (1 / 2 : ℝ) ≤ ‖D.normalizingScalar n *
        momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) 0‖ := by
  let v : Fin 3 → ℂ := fun k => ((saddleScale α₁ α₂ : ℂ) * rho j) ^ k.val
  have hlim : Tendsto (fun n : ℕ => fun k : Fin 3 => D.normalizingScalar n *
      momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) k) atTop (𝓝 v) :=
    tendsto_pi_nhds.mpr (fun k => D.normalized_originalMoment_tendsto h₁ h₂ k)
  have hu : ∀ᶠ n : ℕ in atTop, ‖fun k : Fin 3 => D.normalizingScalar n *
      momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) k‖ < ‖v‖ + 1 :=
    (tendsto_norm.comp hlim).eventually (gt_mem_nhds (lt_add_one _))
  have h0 : Tendsto (fun n : ℕ => ‖D.normalizingScalar n *
      momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) 0‖) atTop (𝓝 1) := by
    simpa only [Fin.val_zero, pow_zero, norm_one, Function.comp_def] using
      tendsto_norm.comp (D.normalized_originalMoment_tendsto h₁ h₂ 0)
  refine ⟨‖v‖ + 1, by linarith [norm_nonneg v], ?_⟩
  filter_upwards [hu, h0.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hl
  exact ⟨fun k => (norm_le_pi_norm _ k).trans hn.le, hl.le⟩

theorem kernel_polynomial_vector_bounds {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ A > 0, ∃ B > 0, ∀ᶠ n : ℕ in atTop,
      ‖D.rawKernel n‖ ≤ A * ‖branchIntegral α₁ α₂ j n‖ ∧
      ‖branchIntegral α₁ α₂ j n‖ ≤ B * (n : ℝ) ^ 3 * ‖D.rawKernel n‖ := by
  obtain ⟨A, hA, B, hB, hscalar⟩ := D.normalizingScalar_polynomial_bounds h₁ h₂
  obtain ⟨M, hM, hvec⟩ := D.eventually_normalized_vector_bounds h₁ h₂
  refine ⟨2 * A, by positivity, 4 * M * B, by positivity, ?_⟩
  filter_upwards [hscalar, hvec, D.eventually_normalizingScalar_ne_zero h₁ h₂,
    eventually_ge_atTop (1 : ℕ)] with n hs hv hane hn
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hRn : largeScale n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le hn1 (by norm_num : (2 / 3 : ℝ) ≤ 1)
  constructor
  · have hf := norm_first_normalized_moment_le n (largeScale n)
      (D.normalizingScalar n) (branchIntegral α₁ α₂ j n)
    have hl : (1 / 2 : ℝ) * ‖D.rawKernel n‖ ≤
        (‖D.normalizingScalar n‖ * ‖D.rawKernel n‖) * ‖branchIntegral α₁ α₂ j n‖ := by
      calc
        _ ≤ ‖D.normalizingScalar n * momentTransform n (largeScale n) (branchIntegral α₁ α₂ j n) 0‖ *
            ‖D.rawKernel n‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
        _ ≤ (‖D.normalizingScalar n‖ * ‖branchIntegral α₁ α₂ j n‖) * ‖D.rawKernel n‖ :=
          mul_le_mul_of_nonneg_right hf (norm_nonneg _)
        _ = _ := by ring
    have hu := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg (branchIntegral α₁ α₂ j n))
    nlinarith
  · calc
      _ ≤ 4 * (n : ℝ) ^ 2 * M * ‖(D.normalizingScalar n)⁻¹‖ :=
        norm_vector_le_of_normalized_moments hn (largeScale_pos hn0) hRn
          (by linarith) hane (branchIntegral α₁ α₂ j n) hv.1
      _ ≤ 4 * (n : ℝ) ^ 2 * M * (B * (n : ℝ) * ‖D.rawKernel n‖) :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = _ := by ring

end ThisWork.CompactSaddleFamily.LocalSaddleData
