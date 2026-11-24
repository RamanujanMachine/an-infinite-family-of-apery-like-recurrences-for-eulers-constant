module

public import ThisWork.HigherRank.OffCutGrowth
public import ThisWork.HigherRank.CenterNormComparison

/-! Off-cut growth for every polynomial center and symbolic positive argument. -/

@[expose] public section
namespace ThisWork.HigherRank

open Filter
open scoped Topology

theorem log_commonScale_center {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (b n : ℕ) :
    Real.log (commonScale r b A z n) = Real.log (commonScale r 0 A z n) +
      Real.log z * ((b : ℝ) * n) := by
  simp only [commonScale, Nat.zero_mul, pow_zero, mul_one]
  rw [Real.log_mul (gammaScale_pos hA n).ne' (pow_pos hz _).ne', Real.log_pow]
  push_cast
  ring

namespace OffCutLocalData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)
include D

theorem logNorm_growth (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      0 < ‖branchIntegral r b A z j n‖ ∧
      |Real.log ‖branchIntegral r b A z j n‖ - Real.log (commonScale r b A z n) +
        largeScale r n * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨C, hC, hb⟩ := D.zeroCenter_logNorm_growth hr hA hz
  let Q := (r - 1 : ℕ) * (Real.log (1 + (b : ℝ)) + 1)
  have hm : 0 ≤ Real.log (1 + (b : ℝ)) := Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg b))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨C + Q * (2 * ((r : ℝ) + 1)), by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  obtain ⟨hIm, hchange⟩ := logNorm_branchIntegral_recenter (by omega : 0 < r) hA b z j hn1 hn.1
  refine ⟨hIm, ?_⟩
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hpol : (r - 1 : ℕ) * (Real.log (1 + (b : ℝ)) + Real.log (n : ℝ)) ≤
      Q * (1 + Real.log (n : ℝ)) := by
    dsimp only [Q]
    nlinarith [mul_nonneg hm hlogn, Nat.cast_nonneg (α := ℝ) (r - 1),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) (r - 1)) (mul_nonneg hm hlogn)]
  have hsmall := (hchange.trans hpol).trans
    (mul_le_mul_of_nonneg_left (one_add_log_nat_le_errorScale hr hn1) hQ)
  rw [log_commonScale_center hA hz]
  have hab := abs_add_le
    (Real.log ‖branchIntegral r 0 A z j n‖ - Real.log (commonScale r 0 A z n) +
      largeScale r n * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re))
    (Real.log ‖branchIntegral r b A z j n‖ - Real.log ‖branchIntegral r 0 A z j n‖ -
      Real.log z * ((b : ℝ) * n))
  have hid (a auxB c d t : ℝ) : (a - c + d) + (auxB - a - t) = auxB - (c + t) + d := by ring
  rw [hid] at hab
  nlinarith [hn.2]

theorem normEstimate (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
      ‖branchIntegral r b A z j n‖ = commonScale r b A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) := by
  obtain ⟨C, hC, hb⟩ := D.logNorm_growth hr hA hz b
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  let E := Real.log ‖branchIntegral r b A z j n‖ - Real.log (commonScale r b A z n) +
    largeScale r n * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)
  refine ⟨E, ?_, ?_⟩
  · simpa only [largeScale_mul_smallParameter r hn0] using hn.2
  · have hS := commonScale_pos hA hz b n
    have hexp : commonScale r b A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) =
          Real.exp (Real.log (commonScale r b A z n) +
            (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E)) := by
      rw [Real.exp_add (Real.log (commonScale r b A z n))
        (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E), Real.exp_log hS]
    rw [show Real.log (commonScale r b A z n) +
      (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) =
        Real.log ‖branchIntegral r b A z j n‖ by dsimp only [E]; ring, Real.exp_log hn.1] at hexp
    exact hexp.symm

end OffCutLocalData
theorem offCut_normEstimate {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z θ : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (j : ℤ) (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi)
    (hj : (r : ℝ) * θ = -2 * Real.pi * j) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
      ‖branchIntegral r b A z j n‖ = commonScale r b A z n *
        Real.exp (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re * largeScale r n + E) := by
  obtain ⟨D⟩ := exists_offCutLocalData hr hA hz j hθ hj
  exact D.normEstimate hr hA hz b

end ThisWork.HigherRank
