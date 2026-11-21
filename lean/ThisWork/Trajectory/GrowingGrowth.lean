module
public import ThisWork.Trajectory.GrowingVectorBounds
public import ThisWork.Trajectory.CanonicalGrowth
public import ThisWork.Trajectory.HankelConjugation
/-! The complete growing-branch norm estimates at arbitrary positive real argument. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

namespace ReflectedSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)

theorem growingSaddleKernel_log_norm_estimate :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖F.growingSaddleKernel n‖ - Real.log (doubleScale m d A₁ A₂ z (F.index n)) -
        2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)| ≤
        C * (1 + Real.log (sqrtScale (F.index n))) := by
  obtain ⟨C, hC, hk⟩ := F.saddleKernel_log_norm_estimate
  refine ⟨C + |Real.log ‖reflectionMomentFactor 0‖|, by positivity, ?_⟩
  filter_upwards [hk, F.eventually_saddleKernel_ne_zero,
    (sqrtScale_tendsto.comp F.index_tendsto).eventually (eventually_ge_atTop (1 : ℝ))] with n hn hK hR
  change 1 ≤ sqrtScale (F.index n) at hR
  rw [growingSaddleKernel, norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr (reflectionMomentFactor_ne_zero 0)) (norm_ne_zero_iff.mpr hK)]
  rw [abs_le] at hn ⊢
  have hlog := Real.log_nonneg hR
  constructor <;> nlinarith [le_abs_self (Real.log ‖reflectionMomentFactor 0‖),
    neg_abs_le (Real.log ‖reflectionMomentFactor 0‖), abs_nonneg (Real.log ‖reflectionMomentFactor 0‖)]

theorem vector_log_norm_estimate (hm : 0 < m) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      0 < ‖branchIntegral m d A₁ A₂ z .one (F.index n)‖ ∧
      |Real.log ‖branchIntegral m d A₁ A₂ z .one (F.index n)‖ -
        Real.log (doubleScale m d A₁ A₂ z (F.index n)) -
          2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)| ≤
        C * (1 + Real.log (F.index n : ℝ)) := by
  obtain ⟨A, hA, B, hB, hb⟩ := F.kernel_polynomial_vector_bounds hm
  obtain ⟨C, hC, hk⟩ := F.growingSaddleKernel_log_norm_estimate
  refine ⟨C + (|Real.log A| + |Real.log B| + 3), by positivity, ?_⟩
  filter_upwards [hb, hk, F.eventually_growingSaddleKernel_ne_zero,
    F.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ))] with n hn hkernel hK hn₁
  have hnorm := log_difference_polynomial_log hA hB (norm_pos_iff.mpr hK) hn₁ hn.1 hn.2
  have hlog : Real.log (sqrtScale (F.index n)) ≤ Real.log (F.index n : ℝ) :=
    Real.log_le_log (sqrtScale_pos (by omega)) (sqrtScale_le_nat hn₁)
  have hker' : |Real.log ‖F.growingSaddleKernel n‖ - Real.log (doubleScale m d A₁ A₂ z (F.index n)) -
      2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)| ≤ C * (1 + Real.log (F.index n : ℝ)) :=
    hkernel.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  refine ⟨hnorm.1, ?_⟩
  have he : Real.log ‖branchIntegral m d A₁ A₂ z .one (F.index n)‖ -
      Real.log (doubleScale m d A₁ A₂ z (F.index n)) -
      2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n) =
      (Real.log ‖branchIntegral m d A₁ A₂ z .one (F.index n)‖ - Real.log ‖F.growingSaddleKernel n‖) +
      (Real.log ‖F.growingSaddleKernel n‖ - Real.log (doubleScale m d A₁ A₂ z (F.index n)) -
        2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hnorm.2 hker').trans_eq (by ring))

end ReflectedSaddleData

/-- The first growing integral has exponent `+2*c*sqrt(n)` with logarithmic error. -/
theorem growing_one_normEstimate {m d : ℕ} {A₁ A₂ z : ℝ}
    (hm : 0 < m) (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (1 + Real.log (n : ℝ)) ∧
      ‖branchIntegral m d A₁ A₂ z .one n‖ = doubleScale m d A₁ A₂ z n *
        Real.exp (2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E) := by
  obtain ⟨F⟩ := exists_reflectedSaddleData hd h₁ h₂ hz m
  obtain ⟨C, hC, hb⟩ := F.vector_log_norm_estimate hm
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  let offset := F.data.shift + F.family.firstIndex
  refine ⟨C, hC, N + offset + 1, fun n hn => ?_⟩
  have hidx : F.index (n - offset) = n := by dsimp only [ReflectedSaddleData.index, offset]; omega
  have hlarge : N ≤ n - offset := by omega
  have hn₀ : 0 < n := by omega
  have h := hN (n - offset) hlarge
  rw [hidx] at h
  let E := Real.log ‖branchIntegral m d A₁ A₂ z .one n‖ -
    Real.log (doubleScale m d A₁ A₂ z n) - 2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n
  refine ⟨E, h.2, ?_⟩
  calc
    _ = Real.exp (Real.log ‖branchIntegral m d A₁ A₂ z .one n‖) := (Real.exp_log h.1).symm
    _ = Real.exp (Real.log (doubleScale m d A₁ A₂ z n)) *
        Real.exp (2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [E]
      ring
    _ = _ := by rw [Real.exp_log (doubleScale_pos hd hn₀ h₁ h₂ hz)]

/-- The conjugate growing branch has exactly the same vector norm. -/
theorem growing_two_normEstimate {m d : ℕ} {A₁ A₂ z : ℝ}
    (hm : 0 < m) (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (1 + Real.log (n : ℝ)) ∧
      ‖branchIntegral m d A₁ A₂ z .two n‖ = doubleScale m d A₁ A₂ z n *
        Real.exp (2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E) := by
  simpa only [norm_branchIntegral_two_eq_one] using growing_one_normEstimate hm hd h₁ h₂ hz

end ThisWork.Trajectory
