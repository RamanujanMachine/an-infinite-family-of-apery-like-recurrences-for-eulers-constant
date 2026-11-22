module

public import ThisWork.HigherRank.ReflectedAnchorNorm

/-! Uniform real-axis Stirling estimates, including points whose scaled
coordinate approaches zero. Only the unscaled coordinate must exceed two. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem gamma_error_and_log_real_segment {R t T : ℝ} (hR : 1 ≤ R)
    (hu : 2 ≤ R * t) (ht : t ≤ T) :
    |Analytic.gammaNormError ((R * t : ℝ) : ℂ)| + |Real.log (R * t)| ≤
      (|Analytic.gammaNormError 2| + 3 + 3 * |Real.log T|) * (1 + Real.log R) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ht0 : 0 < t := (mul_pos_iff_of_pos_left hR0).mp (by linarith : 0 < R * t)
  have hT0 : 0 < T := ht0.trans_le ht
  have he := Analytic.abs_gammaNormError_right (z := ((R * t : ℝ) : ℂ)) (by simpa using hu)
  simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, zero_div, add_zero] at he
  have hl : Real.log (R * t) ≤ Real.log R + |Real.log T| := by
    rw [Real.log_mul hR0.ne' ht0.ne']
    linarith [Real.log_le_log ht0 ht, le_abs_self (Real.log T)]
  rw [abs_of_nonneg (Real.log_nonneg (by linarith : 1 ≤ R * t))]
  nlinarith [Real.log_nonneg hR, mul_nonneg (abs_nonneg (Analytic.gammaNormError 2)) (Real.log_nonneg hR),
    mul_nonneg (abs_nonneg (Real.log T)) (Real.log_nonneg hR)]

theorem uniform_log_norm_reflectedKernel_real_window {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z T : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (hT : 0 < T) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 < t → t ≤ T → 2 ≤ largeScale r n * t →
      |Real.log ‖reflectedKernel r m A z n (-(largeScale r n : ℂ) * (t : ℂ))‖ -
        Real.log (commonScale r m A z n) -
        largeScale r n * ((r : ℝ) * reflectedRealPhase (saddleScale r A z) t)| ≤
          C * (largeScale r n * smallParameter r n) := by
  have hu (i : Fin (r - 1)) := uniform_rightGammaNormError (show 1 ≤ r by omega) (hA i) hT
  choose C hC hb using hu
  let G := (|Analytic.gammaNormError 2| + 3 + 3 * |Real.log T|) * ((r : ℝ) + 1)
  refine ⟨(r : ℝ) * G + ∑ i, C i, add_nonneg (by dsimp only [G]; positivity)
    (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  filter_upwards [Filter.eventually_all.mpr hb, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with n hnC hR hn1 t ht htT hut
  have hR0 : 0 < largeScale r n := zero_lt_one.trans_le hR
  have hslit : -(-(t : ℂ)) ∈ Complex.slitPlane := by
    rw [neg_neg]; exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using ht))
  have hx : ((largeScale r n : ℂ) * (-(t : ℂ))).re < 1 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]; nlinarith
  have he := log_norm_reflectedKernel_error (by omega : 0 < r) hA hz m (by omega : 0 < n) hslit hx
  rw [reflectedPhase_neg_real (by omega : 0 < r) hA hz ht] at he
  simp only [neg_neg] at he
  rw [show (largeScale r n : ℂ) * (-(t : ℂ)) = -(largeScale r n : ℂ) * (t : ℂ) by ring] at he
  rw [he]
  have hg := (gamma_error_and_log_real_segment hR hut htT).trans
    (mul_le_mul_of_nonneg_left (one_add_log_largeScale_le hr hn1)
      (by positivity : 0 ≤ |Analytic.gammaNormError 2| + 3 + 3 * |Real.log T|))
  have hcast : ((largeScale r n * t : ℝ) : ℂ) = (largeScale r n : ℂ) * (t : ℂ) := by push_cast; rfl
  rw [hcast] at hg
  have hlog : Real.log ‖(largeScale r n : ℂ) * (t : ℂ)‖ = Real.log (largeScale r n * t) := by
    rw [← hcast, Complex.norm_of_nonneg (mul_pos hR0 ht).le]
  rw [← hlog] at hg
  have hupper : (∑ i, |rightGammaNormError r (A i) n (-(t : ℂ))|) ≤
      (∑ i, C i) * (largeScale r n * smallParameter r n) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hnC i (-(t : ℂ)) (by
      rw [norm_neg, Complex.norm_of_nonneg ht.le]; exact htT))
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ)
    (f := fun i => rightGammaNormError r (A i) n (-(t : ℂ)))
  have hlow := abs_sub (-(r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (t : ℂ)))
    ((r : ℝ) * Real.log ‖(largeScale r n : ℂ) * (t : ℂ)‖)
  have hadd := abs_add_le (-(r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (t : ℂ)) -
    (r : ℝ) * Real.log ‖(largeScale r n : ℂ) * (t : ℂ)‖)
      (∑ i, rightGammaNormError r (A i) n (-(t : ℂ)))
  simp only [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hlow
  have hh := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  dsimp only [G] at *
  nlinarith

end ThisWork.HigherRank
