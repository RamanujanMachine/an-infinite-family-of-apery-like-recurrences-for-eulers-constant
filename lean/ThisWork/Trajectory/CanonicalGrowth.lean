module
public import ThisWork.Trajectory.CanonicalVectorBounds
/-! The canonical growth rate for two equal minimal lower slopes. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

theorem log_difference_polynomial_log {x K A B : ℝ} {n : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K) (hn : 1 ≤ n)
    (hl : K ≤ A * x) (hu : x ≤ B * (n : ℝ) ^ 3 * K) :
    0 < x ∧ |Real.log x - Real.log K| ≤
      (|Real.log A| + |Real.log B| + 3) * (1 + Real.log (n : ℝ)) := by
  have hx : 0 < x := by
    by_contra! hx
    have hh := mul_nonpos_of_nonneg_of_nonpos hA.le hx
    linarith
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hll := Real.log_le_log hK hl
  rw [Real.log_mul hA.ne' hx.ne'] at hll
  have hlu := Real.log_le_log hx hu
  rw [Real.log_mul (mul_ne_zero hB.ne' (pow_ne_zero 3 hn₀.ne')) hK.ne',
    Real.log_mul hB.ne' (pow_ne_zero 3 hn₀.ne'), Real.log_pow] at hlu
  norm_num only [Nat.cast_ofNat] at hlu
  have hlog := Real.log_nonneg hn₁
  refine ⟨hx, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    nlinarith [le_abs_self (Real.log A), le_abs_self (Real.log B),
      abs_nonneg (Real.log A), abs_nonneg (Real.log B)]

namespace CanonicalSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : CanonicalSaddleData m d A₁ A₂ z)

theorem vector_log_norm_estimate (hm : 0 < m) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      0 < ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ ∧
      |Real.log ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ -
        Real.log (doubleScale m d A₁ A₂ z (F.index n)) +
          2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)| ≤
        C * (1 + Real.log (F.index n : ℝ)) := by
  obtain ⟨A, hA, B, hB, hb⟩ := F.kernel_polynomial_vector_bounds hm
  obtain ⟨C, hC, hk⟩ := uniform_log_norm_canonical_kernel_near_saddle
    F.d_pos F.A₁_pos F.A₂_pos F.z_pos F.family.errorConstant_nonneg m
  refine ⟨C + (|Real.log A| + |Real.log B| + 3), by positivity, ?_⟩
  filter_upwards [hb, F.index_tendsto.eventually hk, F.eventually_saddleKernel_ne_zero,
    F.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ))] with n hn hkernel hK hn₁
  have hnorm := log_difference_polynomial_log hA hB (norm_pos_iff.mpr hK) hn₁ hn.1 hn.2
  have hker := hkernel (F.center n) (F.center_mem n) (F.family.displacement (n + F.data.shift))
  have hlog : Real.log (sqrtScale (F.index n)) ≤ Real.log (F.index n : ℝ) :=
    Real.log_le_log (sqrtScale_pos (by omega)) (sqrtScale_le_nat hn₁)
  have hker' : |Real.log ‖F.saddleKernel n‖ - Real.log (doubleScale m d A₁ A₂ z (F.index n)) +
      2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)| ≤ C * (1 + Real.log (F.index n : ℝ)) :=
    hker.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  refine ⟨hnorm.1, ?_⟩
  have he : Real.log ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ -
      Real.log (doubleScale m d A₁ A₂ z (F.index n)) +
      2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n) =
      (Real.log ‖branchIntegral m d A₁ A₂ z .three (F.index n)‖ - Real.log ‖F.saddleKernel n‖) +
      (Real.log ‖F.saddleKernel n‖ - Real.log (doubleScale m d A₁ A₂ z (F.index n)) +
        2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hnorm.2 hker').trans_eq (by ring))

end CanonicalSaddleData

/-- The canonical integral has exponent `-2*c*sqrt(n)` with only logarithmic error. -/
theorem canonical_normEstimate {m d : ℕ} {A₁ A₂ z : ℝ}
    (hm : 0 < m) (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (1 + Real.log (n : ℝ)) ∧
      ‖branchIntegral m d A₁ A₂ z .three n‖ = doubleScale m d A₁ A₂ z n *
        Real.exp (-2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E) := by
  obtain ⟨F⟩ := exists_canonicalSaddleData hd h₁ h₂ hz m
  obtain ⟨C, hC, hb⟩ := F.vector_log_norm_estimate hm
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  let offset := F.data.shift + F.family.firstIndex
  refine ⟨C, hC, N + offset + 1, fun n hn => ?_⟩
  have hidx : F.index (n - offset) = n := by dsimp only [CanonicalSaddleData.index, offset]; omega
  have hlarge : N ≤ n - offset := by omega
  have hn₀ : 0 < n := by omega
  have h := hN (n - offset) hlarge
  rw [hidx] at h
  let E := Real.log ‖branchIntegral m d A₁ A₂ z .three n‖ -
    Real.log (doubleScale m d A₁ A₂ z n) + 2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n
  refine ⟨E, h.2, ?_⟩
  calc
    _ = Real.exp (Real.log ‖branchIntegral m d A₁ A₂ z .three n‖) := (Real.exp_log h.1).symm
    _ = Real.exp (Real.log (doubleScale m d A₁ A₂ z n)) *
        Real.exp (-2 * doubleSaddleScale d A₁ A₂ z * sqrtScale n + E) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [E]
      ring
    _ = _ := by rw [Real.exp_log (doubleScale_pos hd hn₀ h₁ h₂ hz)]

end ThisWork.Trajectory
