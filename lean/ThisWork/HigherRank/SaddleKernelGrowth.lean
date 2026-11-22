module

public import ThisWork.HigherRank.AnchorTransfer
public import ThisWork.HigherRank.OffCutLocalData

/-! Quantitative kernel growth at moving saddles, with the common Gamma
normalization and the limiting saddle value kept explicit. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology OnePoint

theorem exists_local_limitingPhase_lipschitz (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ)
    {ζ : ℂ} (hζ : ζ ∈ Complex.slitPlane) :
    ∃ d > 0, ∃ L ≥ 0, ∀ s ∈ ball ζ d,
      ‖limitingPhase r A z j s - limitingPhase r A z j ζ‖ ≤ ‖s - ζ‖ * L := by
  obtain ⟨d, hd, κ, hκ, η, hη, _, _, hregion⟩ := exists_local_slit_region hζ
  have hclosed : closedBall ζ d ⊆ Complex.slitPlane := fun s hs =>
    region_mem_slitPlane hκ hη (hregion s hs).2
  have hEq : DifferentiableOn ℂ (limitingEquation r A z j) Complex.slitPlane :=
    fun _ hs => (hasDerivAt_limitingEquation r A z j hs).differentiableAt.differentiableWithinAt
  obtain ⟨L, hL⟩ := (isCompact_closedBall ζ d).exists_bound_of_continuousOn (hEq.continuousOn.mono hclosed)
  refine ⟨d, hd, max 0 L, le_max_left _ _, fun s hs => ?_⟩
  have h := Analytic.norm_primitive_sub_le_ball (q := fun _ : ℂ => (0 : ℂ))
    (mem_ball_self hd) hs
    (fun t ht => hasDerivAt_limitingPhase r A z j (hclosed (ball_subset_closedBall ht)))
    (fun t _ => hasDerivAt_const t (0 : ℂ))
    (by simpa only [sub_zero] using (hEq.continuousOn.mono
      (fun _ ht => hclosed (ball_subset_closedBall ht))))
    (fun t ht => by simpa only [sub_zero] using
      (hL t (ball_subset_closedBall ht)).trans (le_max_right 0 L))
  simpa only [sub_self, sub_zero] using h

theorem uniform_log_norm_kernel_near_saddle {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z a b : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (ha : 0 < a)
    (m : ℕ) (j : ℤ) (E : ℝ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ σ : ℂ, ‖σ - parabolicPoint a b‖ ≤ E * smallParameter r n →
      |Real.log ‖kernel r m A z j n ((largeScale r n : ℂ) * σ)‖ - Real.log (commonScale r m A z n) -
        largeScale r n * (limitingPhase r A z j (parabolicPoint a b)).re| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨Ca, hCa, hanchor⟩ := uniform_log_norm_kernel_parabola hr hA hz m j ha (abs_nonneg b)
  obtain ⟨d, hd, L, hL, hphase⟩ := exists_local_limitingPhase_lipschitz r A z j (parabolicPoint_mem_slitPlane ha b)
  have ht : Tendsto (fun n => E * smallParameter r n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (smallParameter_tendsto (show 0 < r by omega)).const_mul E
  refine ⟨Ca + L * |E|, by positivity, ?_⟩
  filter_upwards [hanchor, ht.eventually_lt_const (lt_min hd (by positivity : 0 < a ^ 2 / 8)),
    eventually_gt_atTop (0 : ℕ)] with n hn hsmall hn0 σ hσ
  have hδ : ‖σ - parabolicPoint a b‖ ≤ a ^ 2 / 8 := hσ.trans
    (le_of_lt (hsmall.trans_le (min_le_right _ _)))
  have hs : σ ∈ ball (parabolicPoint a b) d := by
    rw [mem_ball, dist_eq_norm]
    exact hσ.trans_lt (hsmall.trans_le (min_le_left _ _))
  have he := hn (σ - parabolicPoint a b) hδ b le_rfl
  rw [sub_add_cancel] at he
  have hp := (Complex.abs_re_le_norm (limitingPhase r A z j σ -
    limitingPhase r A z j (parabolicPoint a b))).trans
      ((hphase σ hs).trans (mul_le_mul_of_nonneg_right hσ hL))
  rw [Complex.sub_re] at hp
  have hR : 0 ≤ largeScale r n := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _).le
  have hε : 0 ≤ smallParameter r n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hE := mul_le_mul_of_nonneg_right (le_abs_self E) hε
  have hdiff := mul_le_mul_of_nonneg_left hp hR
  exact abs_le.mpr ⟨by nlinarith [(abs_le.mp he).1, (abs_le.mp hp).1,
    mul_le_mul_of_nonneg_left hE (mul_nonneg hR hL)],
    by nlinarith [(abs_le.mp he).2, (abs_le.mp hp).2,
      mul_le_mul_of_nonneg_left hE (mul_nonneg hR hL)]⟩

namespace OffCutLocalData

theorem saddleKernel_growth {r : ℕ} (hr : 3 ≤ r) {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ}
    (D : OffCutLocalData r A z j θ) (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖kernel r m A z j (n + D.family.firstIndex)
        ((largeScale r (n + D.family.firstIndex) : ℂ) * D.family.saddle n)‖ -
          Real.log (commonScale r m A z (n + D.family.firstIndex)) +
          largeScale r (n + D.family.firstIndex) * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re)| ≤
            C * (largeScale r (n + D.family.firstIndex) * smallParameter r (n + D.family.firstIndex)) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_near_saddle (b := D.b) hr hA hz D.a_pos m j D.family.errorConstant
  have hzero : limitingEquation r A z j (parabolicPoint D.a D.b) = 0 := by
    simpa only [parameterEquation,
      Analytic.sequenceFamily_infty, D.family.saddle_limit] using D.family.equation_zero ∞
  have hp : (limitingPhase r A z j (parabolicPoint D.a D.b)).re =
      -(r : ℝ) * saddleScale r A z * (Phase.rho θ).re := by
    rw [limitingPhase, hzero, D.saddle_eq]
    simp only [zero_sub, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, neg_zero]
    ring
  refine ⟨C, hC, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat D.family.firstIndex).eventually hb] with n hn
  have he := hn (D.family.saddle n) (D.family.displacement n)
  rw [hp] at he
  convert he using 1
  congr 1
  ring

end OffCutLocalData
end ThisWork.HigherRank
