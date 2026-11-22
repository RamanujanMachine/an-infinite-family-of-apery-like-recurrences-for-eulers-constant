module

public import ThisWork.HigherRank.ReflectedKernelNorm
public import ThisWork.HigherRank.AnchorNorm

/-! The absolute growth of the positive reflected kernel at its real saddle. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_log_norm_reflectedKernel_negative_anchor {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z q : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (hq : 0 < q) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖reflectedKernel r m A z n ((largeScale r n : ℂ) * (-(q : ℂ)))‖ -
        Real.log (commonScale r m A z n) - largeScale r n * (reflectedPhase r A z (-(q : ℂ))).re| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨G, hG, hg⟩ := uniform_gamma_error_and_log_positive_anchor hr hq
  have hu (i : Fin (r - 1)) := uniform_rightGammaNormError (show 1 ≤ r by omega) (hA i) hq
  choose C hC hb using hu
  refine ⟨(r : ℝ) * G + ∑ i, C i,
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hG) (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  filter_upwards [hg, Filter.eventually_all.mpr hb, eventually_gt_atTop (0 : ℕ)] with n hnG hnC hn0
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hslit : -(-(q : ℂ)) ∈ Complex.slitPlane := by
    rw [neg_neg]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hq))
  have hx : ((largeScale r n : ℂ) * (-(q : ℂ))).re < 1 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    nlinarith [mul_pos hR hq]
  rw [log_norm_reflectedKernel_error (by omega : 0 < r) hA hz m hn0 hslit hx]
  simp only [neg_neg]
  have hupper : (∑ i, |rightGammaNormError r (A i) n (-(q : ℂ))|) ≤
      (∑ i, C i) * (largeScale r n * smallParameter r n) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hnC i (-(q : ℂ)) (by rw [norm_neg, Complex.norm_of_nonneg hq.le]))
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ)
    (f := fun i => rightGammaNormError r (A i) n (-(q : ℂ)))
  have hlow := abs_sub (-(r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (q : ℂ)))
    ((r : ℝ) * Real.log ‖(largeScale r n : ℂ) * (q : ℂ)‖)
  have hadd := abs_add_le (-(r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (q : ℂ)) -
    (r : ℝ) * Real.log ‖(largeScale r n : ℂ) * (q : ℂ)‖)
      (∑ i, rightGammaNormError r (A i) n (-(q : ℂ)))
  simp only [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hlow
  nlinarith [mul_le_mul_of_nonneg_left hnG (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem reflectedKernel_saddle_growth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖reflectedKernel r m A z n
        ((largeScale r n : ℂ) * (-(saddleScale r A z : ℂ)))‖ -
        Real.log (commonScale r m A z n) - (r : ℝ) * saddleScale r A z * largeScale r n| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_reflectedKernel_negative_anchor hr hA hz (saddleScale_pos hA hz) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with n hn
  rw [reflectedPhase_saddle (by omega : 0 < r) hA hz] at hn
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hn
  convert hn using 1
  congr 1
  ring

end ThisWork.HigherRank
