module

public import ThisWork.HigherRank.OffCutGlobalRemainder
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Gaussian-normalized moment limits on the full off-cut parabolic contour,
including its infinite tails. -/

@[expose] public section
namespace ThisWork.HigherRank.OffCutLocalData

open Set Filter Metric
open scoped Topology

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

noncomputable def gaussianFactor (n : ℕ) : ℂ :=
  D.localData.quadraticRoot n *
    (((largeScale r (D.index n)) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)

noncomputable def normalizedGlobalMoment (B : ℝ) (b k n : ℕ) : ℂ :=
  D.gaussianFactor n *
    (parabolicPowerMoment r b A z j (D.index n) k D.a B (D.translation n) / D.saddleKernel b n)

theorem exists_normalizedGlobalMoment_tendsto (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b k : ℕ) :
    ∃ B > 0, Tendsto (D.normalizedGlobalMoment B b k) atTop
      (𝓝 (((saddleScale r A z : ℂ) * Phase.rho θ) ^ k)) := by
  obtain ⟨B, hB, g, hg, C, hC, hrem⟩ := D.exists_full_moment_remainder_bound hr hA hz b k
  obtain ⟨U, hU, hroot⟩ := D.localData.uniform_quadraticRoot_bounds D.tangent_ne_zero
  have hU0 : 0 ≤ U := by linarith
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hRlim : Tendsto (fun n => largeScale r (D.index n)) atTop atTop :=
    (largeScale_tendsto (show 1 < r by omega)).comp D.index_tendsto
  have hlocal := D.localData.eventually_localKernelMoment_eq_phase (by omega : 0 < r) hA D.disk_slit b k
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖D.normalizedGlobalMoment B b k n -
        D.localData.normalizedLocalMoment (largeScale r (D.index n)) k n‖ ≤
        (U * C / Real.Gamma (1 / 2 : ℝ)) *
          ((largeScale r (D.index n)) ^ (1 / 2 : ℝ) * Real.exp (-g * largeScale r (D.index n))) := by
    filter_upwards [hrem, hlocal, D.eventually_saddleKernel_ne_zero (by omega : 0 < r) hA b,
      hRlim.eventually (eventually_gt_atTop (0 : ℝ))] with n hnR hnL hnK hR
    let R := largeScale r (D.index n)
    let P := parabolicPowerMoment r b A z j (D.index n) k D.a B (D.translation n)
    let L := D.localData.localKernelMoment b (D.index n) (D.center n) k
    let K := D.saddleKernel b n
    have hK : 0 < ‖K‖ := norm_pos_iff.mpr hnK
    have hK0 : K ≠ 0 := hnK
    have hKL : L = K * D.localData.localMoment R k n := hnL
    have hid : D.normalizedGlobalMoment B b k n - D.localData.normalizedLocalMoment R k n =
        D.gaussianFactor n * ((P - L) / K) := by
      change D.gaussianFactor n * (P / K) - D.gaussianFactor n * D.localData.localMoment R k n = _
      rw [hKL]
      field_simp [hK0]
    have hquot : ‖(P - L) / K‖ ≤ C * Real.exp (-g * R) := by
      rw [norm_div]
      apply (div_le_iff₀ hK).mpr
      change ‖P - L‖ ≤ C * ‖K‖ * Real.exp (-g * R) at hnR
      nlinarith
    have hfactor : ‖D.gaussianFactor n‖ ≤ U * (R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ)) := by
      rw [gaussianFactor, norm_mul, Complex.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hroot n).1 (by positivity)
    rw [hid, norm_mul]
    calc
      _ ≤ (U * (R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ))) * (C * Real.exp (-g * R)) :=
        mul_le_mul hfactor hquot (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hdecay : Tendsto (fun n => (U * C / Real.Gamma (1 / 2 : ℝ)) *
      ((largeScale r (D.index n)) ^ (1 / 2 : ℝ) * Real.exp (-g * largeScale r (D.index n)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2 : ℝ) g hg).comp hRlim).const_mul
        (U * C / Real.Gamma (1 / 2 : ℝ))
  have hdiff := squeeze_zero_norm' hsmall hdecay
  refine ⟨B, hB, ?_⟩
  change Tendsto (fun n => D.normalizedGlobalMoment B b k n) atTop _
  simpa only [index, sub_add_cancel, zero_add] using
    hdiff.add (D.normalizedLocalMoment_tendsto (by omega : 1 < r) k)

end ThisWork.HigherRank.OffCutLocalData
