module

public import ThisWork.HigherRank.OffCutVectorBounds
public import ThisWork.HigherRank.SaddleKernelGrowth
public import ThisWork.HigherRank.BoundaryScales

/-! Growth of the actual off-cut integral vectors, obtained from the full
moment limits and the absolute saddle-kernel estimates. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem logarithmic_error_of_polynomial_bounds {x K L U : ℝ} {n p : ℕ}
    (hL : 0 < L) (hU : 0 < U) (hK : 0 < K) (hn : 1 ≤ n)
    (hl : K ≤ L * x) (hu : x ≤ U * (n : ℝ) ^ p * K) :
    0 < x ∧ |Real.log x - Real.log K| ≤
      (|Real.log L| + |Real.log U| + (p : ℝ)) * (1 + Real.log (n : ℝ)) := by
  have hx : 0 < x := by
    by_contra! hx
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hL.le hx]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hl' := Real.log_le_log hK hl
  rw [Real.log_mul hL.ne' hx.ne'] at hl'
  have hu' := Real.log_le_log hx hu
  rw [Real.log_mul (mul_pos hU (pow_pos hn0 p)).ne' hK.ne',
    Real.log_mul hU.ne' (pow_pos hn0 p).ne', Real.log_pow] at hu'
  refine ⟨hx, abs_le.mpr ⟨?_, ?_⟩⟩
  · nlinarith [le_abs_self (Real.log L), abs_nonneg (Real.log U), Nat.cast_nonneg (α := ℝ) p,
      mul_nonneg (abs_nonneg (Real.log L)) hlogn,
      mul_nonneg (abs_nonneg (Real.log U)) hlogn,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hlogn]
  · nlinarith [le_abs_self (Real.log U), abs_nonneg (Real.log L), Nat.cast_nonneg (α := ℝ) p,
      mul_nonneg (abs_nonneg (Real.log L)) hlogn, mul_nonneg (abs_nonneg (Real.log U)) hlogn]

namespace OffCutLocalData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

include D

theorem zeroCenter_logNorm_growth (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      0 < ‖branchIntegral r 0 A z j n‖ ∧
      |Real.log ‖branchIntegral r 0 A z j n‖ - Real.log (commonScale r 0 A z n) +
        largeScale r n * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨L, hL, U, hU, hvec⟩ := D.kernel_polynomial_vector_bounds hr hA hz
  obtain ⟨C, hC, hkernel⟩ := D.saddleKernel_growth hr hA hz 0
  let Q := |Real.log L| + |Real.log U| + (r : ℝ)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let E := C + Q * (2 * ((r : ℝ) + 1))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hindexed : ∀ᶠ n : ℕ in atTop,
      0 < ‖branchIntegral r 0 A z j (D.index n)‖ ∧
      |Real.log ‖branchIntegral r 0 A z j (D.index n)‖ - Real.log (commonScale r 0 A z (D.index n)) +
        largeScale r (D.index n) * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)| ≤
          E * (largeScale r (D.index n) * smallParameter r (D.index n)) := by
    filter_upwards [hvec, (tendsto_add_atTop_nat D.localData.shift).eventually hkernel,
      D.eventually_saddleKernel_ne_zero (by omega : 0 < r) hA 0,
      D.index_tendsto.eventually (eventually_ge_atTop (1 : ℕ))] with n hnV hnK hn0 hn1
    have hlog := logarithmic_error_of_polynomial_bounds hL hU (norm_pos_iff.mpr hn0) hn1 hnV.1 hnV.2
    refine ⟨hlog.1, ?_⟩
    have herror := hlog.2.trans (mul_le_mul_of_nonneg_left (one_add_log_nat_le_errorScale hr hn1) hQ)
    have hkernel' : |Real.log ‖D.saddleKernel 0 n‖ - Real.log (commonScale r 0 A z (D.index n)) +
        largeScale r (D.index n) * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)| ≤
          C * (largeScale r (D.index n) * smallParameter r (D.index n)) := hnK
    have hadd := abs_add_le (Real.log ‖branchIntegral r 0 A z j (D.index n)‖ - Real.log ‖D.saddleKernel 0 n‖)
      (Real.log ‖D.saddleKernel 0 n‖ - Real.log (commonScale r 0 A z (D.index n)) +
        largeScale r (D.index n) * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re))
    have hid (a b c d : ℝ) : (a - b) + (b - c + d) = a - c + d := by ring
    rw [hid] at hadd
    dsimp only [E, Q] at *
    nlinarith
  refine ⟨E, hE, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hindexed
  refine eventually_atTop.mpr ⟨N + D.offset, fun n hn => ?_⟩
  have hb := hN (n - D.offset) (by omega)
  simpa only [D.index_eq_add_offset, Nat.sub_add_cancel (show D.offset ≤ n by omega)] using hb

theorem zeroCenter_normEstimate (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
      ‖branchIntegral r 0 A z j n‖ = commonScale r 0 A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) := by
  obtain ⟨C, hC, hb⟩ := D.zeroCenter_logNorm_growth hr hA hz
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  let E := Real.log ‖branchIntegral r 0 A z j n‖ - Real.log (commonScale r 0 A z n) +
    largeScale r n * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)
  refine ⟨E, ?_, ?_⟩
  · simpa only [largeScale_mul_smallParameter r hn0] using hn.2
  · have hS := commonScale_pos hA hz 0 n
    have hexp : commonScale r 0 A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) =
          Real.exp (Real.log (commonScale r 0 A z n) +
            (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E)) := by
      rw [Real.exp_add (Real.log (commonScale r 0 A z n))
        (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E), Real.exp_log hS]
    rw [show Real.log (commonScale r 0 A z n) +
      (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) =
        Real.log ‖branchIntegral r 0 A z j n‖ by dsimp only [E]; ring, Real.exp_log hn.1] at hexp
    exact hexp.symm

end OffCutLocalData
end ThisWork.HigherRank
