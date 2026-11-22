module

public import ThisWork.HigherRank.KernelNorm
public import ThisWork.ScaledGammaNorm

/-! Absolute normalization at a positive real anchor. Off-cut saddles can
then be reached by integrating the exact logarithmic derivative. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_log_norm_kernel_positive_anchor {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z q : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (hq : 0 < q)
    (m : ℕ) (j : ℤ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖kernel r m A z j n ((largeScale r n : ℂ) * (q : ℂ))‖ -
        Real.log (commonScale r m A z n) - largeScale r n * (limitingPhase r A z j q).re| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨G, hG, hg⟩ := Analytic.uniform_scaled_gammaNormError_right hq hq
  have hu (i : Fin (r - 1)) := uniform_rightGammaNormError (show 1 ≤ r by omega) (hA i) hq
  choose C hC hb using hu
  refine ⟨(r : ℝ) * G * ((r : ℝ) + 1) + ∑ i, C i,
    add_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  filter_upwards [(largeScale_tendsto (show 1 < r by omega)).eventually hg,
    Filter.eventually_all.mpr hb, eventually_scaled_slit_in_kernelDomain (by omega : 0 < r) hA q,
    eventually_ge_atTop (1 : ℕ)] with n hnG hnC hdom hn1
  have hqnorm : ‖(q : ℂ)‖ ≤ q := by rw [Complex.norm_of_nonneg hq.le]
  have hGamma : |Analytic.gammaNormError ((largeScale r n : ℂ) * (q : ℂ))| ≤
      (G * ((r : ℝ) + 1)) * (largeScale r n * smallParameter r n) := by
    calc
      _ ≤ G * (1 + Real.log (largeScale r n)) := hnG.2 q hqnorm (by simp)
      _ ≤ G * (((r : ℝ) + 1) * (largeScale r n * smallParameter r n)) :=
        mul_le_mul_of_nonneg_left (one_add_log_largeScale_le hr hn1) hG
      _ = _ := by ring
  have hupper : (∑ i, |rightGammaNormError r (A i) n q|) ≤
      (∑ i, C i) * (largeScale r n * smallParameter r n) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hnC i q hqnorm)
  have hx : (largeScale r n : ℂ) * (q : ℂ) ∈ kernelDomain r A n :=
    hdom q (by simp) (Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hq)))
  have he := log_norm_kernel_error (by omega : 0 < r) hA m z j (by omega : 0 < n)
    (Complex.ofReal_ne_zero.mpr hq.ne') hx
  have herr : Real.log ‖kernel r m A z j n ((largeScale r n : ℂ) * (q : ℂ))‖ -
      Real.log (commonScale r m A z n) - largeScale r n * (limitingPhase r A z j q).re =
      (r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (q : ℂ)) +
        ∑ i, rightGammaNormError r (A i) n q := by
    rw [log_commonScale hA hz]
    linarith
  rw [herr]
  have hmain := mul_le_mul_of_nonneg_left hGamma (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => rightGammaNormError r (A i) n q)
  have hadd := abs_add_le ((r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (q : ℂ)))
    (∑ i, rightGammaNormError r (A i) n q)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hadd
  nlinarith

theorem uniform_gamma_error_and_log_positive_anchor {r : ℕ} (hr : 3 ≤ r)
    {q : ℝ} (hq : 0 < q) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Analytic.gammaNormError ((largeScale r n : ℂ) * (q : ℂ))| +
        |Real.log ‖(largeScale r n : ℂ) * (q : ℂ)‖| ≤ C * (largeScale r n * smallParameter r n) := by
  obtain ⟨G, hG, hg⟩ := Analytic.uniform_scaled_gammaNormError_right hq hq
  refine ⟨(G + 1 + |Real.log q|) * ((r : ℝ) + 1), by positivity, ?_⟩
  filter_upwards [(largeScale_tendsto (show 1 < r by omega)).eventually hg,
    (largeScale_tendsto (show 1 < r by omega)).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hnG hR1 hn1
  have hR := hnG.1
  have hlog : |Real.log ‖(largeScale r n : ℂ) * (q : ℂ)‖| ≤ Real.log (largeScale r n) + |Real.log q| := by
    rw [norm_mul, Complex.norm_of_nonneg hR.le, Complex.norm_of_nonneg hq.le,
      Real.log_mul hR.ne' hq.ne']
    exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (Real.log_nonneg hR1)])
  have hgerr := hnG.2 q (by rw [Complex.norm_of_nonneg hq.le]) (by simp)
  have hbound := mul_le_mul_of_nonneg_left (one_add_log_largeScale_le hr hn1)
    (show 0 ≤ G + 1 + |Real.log q| by positivity)
  nlinarith [Real.log_nonneg hR1, mul_nonneg (abs_nonneg (Real.log q)) (Real.log_nonneg hR1)]

end ThisWork.HigherRank
