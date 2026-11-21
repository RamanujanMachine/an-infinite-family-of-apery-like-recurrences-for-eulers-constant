module
public import ThisWork.Trajectory.SqrtNormalizerNorm
public import ThisWork.IntegralNormBounds
/-! Polynomial norm comparison for the canonical trajectory vector. -/
public section
namespace ThisWork.Trajectory.CanonicalSaddleData
open Set Filter Metric Analytic
open scoped Topology OnePoint
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : CanonicalSaddleData m d A₁ A₂ z)
theorem eventually_normalized_vector_bounds  :
    ∃ M ≥ 1, ∀ᶠ n : ℕ in atTop,
      (∀ k : Fin 3, ‖F.normalizingScalar n *
        momentTransform (m * F.index n) (sqrtScale (F.index n)) (branchIntegral m d A₁ A₂ z .three (F.index n)) k‖ ≤ M) ∧
      (1 / 2 : ℝ) ≤ ‖F.normalizingScalar n *
        momentTransform (m * F.index n) (sqrtScale (F.index n)) (branchIntegral m d A₁ A₂ z .three (F.index n)) 0‖ := by
  let v : Fin 3 → ℂ := fun k => (doubleSaddleScale d A₁ A₂ z : ℂ) ^ k.val
  have hlim : Tendsto (fun n : ℕ => fun k : Fin 3 => F.normalizingScalar n *
      momentTransform (m * F.index n) (sqrtScale (F.index n)) (branchIntegral m d A₁ A₂ z .three (F.index n)) k) atTop (𝓝 v) :=
    tendsto_pi_nhds.mpr (fun k => F.normalized_originalMoment_tendsto k)
  have hu : ∀ᶠ n : ℕ in atTop, ‖fun k : Fin 3 => F.normalizingScalar n *
      momentTransform (m * F.index n) (sqrtScale (F.index n)) (branchIntegral m d A₁ A₂ z .three (F.index n)) k‖ < ‖v‖ + 1 :=
    (tendsto_norm.comp hlim).eventually (gt_mem_nhds (lt_add_one _))
  have h0 : Tendsto (fun n : ℕ => ‖F.normalizingScalar n *
      momentTransform (m * F.index n) (sqrtScale (F.index n)) (branchIntegral m d A₁ A₂ z .three (F.index n)) 0‖) atTop (𝓝 1) := by
    simpa only [Fin.val_zero, pow_zero, norm_one, Function.comp_def] using
      tendsto_norm.comp (F.normalized_originalMoment_tendsto 0)
  refine ⟨‖v‖ + 1, by linarith [norm_nonneg v], ?_⟩
  filter_upwards [hu, h0.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn hl
  exact ⟨fun k => (norm_le_pi_norm _ k).trans hn.le, hl.le⟩

theorem kernel_polynomial_vector_bounds (hm : 0 < m) :
    ∃ A > 0, ∃ B > 0, ∀ᶠ n : ℕ in atTop,
      ‖F.saddleKernel n‖ ≤ A * ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ ∧
      ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ ≤ B * (F.index n : ℝ) ^ 3 * ‖F.saddleKernel n‖ := by
  obtain ⟨A, hA, B, hB, hscalar⟩ := F.normalizingScalar_polynomial_bounds
  obtain ⟨M, hM, hvec⟩ := F.eventually_normalized_vector_bounds
  refine ⟨2 * A, by positivity, 4 * M * B * (m : ℝ) ^ 2, by positivity, ?_⟩
  filter_upwards [hscalar, hvec, F.eventually_normalizingScalar_ne_zero,
    F.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ))] with n hs hv hane hn
  have hn0 : 0 < F.index n := by omega
  have hn1 : 1 ≤ (F.index n : ℝ) := by exact_mod_cast hn
  have hmn : 1 ≤ m * F.index n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' (by omega))
  have hRn : sqrtScale (F.index n) ≤ (m * F.index n : ℕ) :=
    (sqrtScale_le_nat hn).trans (by exact_mod_cast Nat.le_mul_of_pos_left (F.index n) hm)
  constructor
  · have hf := norm_first_normalized_moment_le (m * F.index n) (sqrtScale (F.index n))
      (F.normalizingScalar n) (branchIntegral m d A₁ A₂ z .three (F.index n))
    have hl : (1 / 2 : ℝ) * ‖F.saddleKernel n‖ ≤
        (‖F.normalizingScalar n‖ * ‖F.saddleKernel n‖) * ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ := by
      calc
        _ ≤ ‖F.normalizingScalar n * momentTransform (m * F.index n) (sqrtScale (F.index n)) (branchIntegral m d A₁ A₂ z .three (F.index n)) 0‖ *
            ‖F.saddleKernel n‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
        _ ≤ (‖F.normalizingScalar n‖ * ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖) * ‖F.saddleKernel n‖ :=
          mul_le_mul_of_nonneg_right hf (norm_nonneg _)
        _ = _ := by ring
    have hu := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg (branchIntegral m d A₁ A₂ z .three (F.index n)))
    nlinarith
  · calc
      _ ≤ 4 * (m * F.index n : ℕ) ^ 2 * M * ‖(F.normalizingScalar n)⁻¹‖ :=
        norm_vector_le_of_normalized_moments hmn (sqrtScale_pos hn0) hRn
          (by linarith) hane (branchIntegral m d A₁ A₂ z .three (F.index n)) hv.1
      _ ≤ 4 * (m * F.index n : ℕ) ^ 2 * M * (B * (F.index n : ℝ) * ‖F.saddleKernel n‖) :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = _ := by push_cast; ring


end ThisWork.Trajectory.CanonicalSaddleData
