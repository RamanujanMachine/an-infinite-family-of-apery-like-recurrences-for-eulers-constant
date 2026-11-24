module

public import ThisWork.HigherRank.PascalTranslation

/-! Changes of moment center preserve logarithmic growth up to `O(log n)`. -/

@[expose] public section
namespace ThisWork.HigherRank

theorem logarithmic_error_of_symmetric_comparison {x y P : ℝ}
    (hy : 0 < y) (hP : 0 < P) (hl : y ≤ P * x) (hu : x ≤ P * y) :
    0 < x ∧ |Real.log x - Real.log y| ≤ Real.log P := by
  have hx : 0 < x := by
    by_contra! hx
    exact (not_le_of_gt hy) (hl.trans (mul_nonpos_of_nonneg_of_nonpos hP.le hx))
  have hlo := Real.log_le_log hy hl
  have hup := Real.log_le_log hx hu
  rw [Real.log_mul hP.ne' hx.ne'] at hlo
  rw [Real.log_mul hP.ne' hy.ne'] at hup
  exact ⟨hx, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem norm_branchIntegral_recenter_bounds {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i)
    (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) :
    let x := Real.exp (-(Real.log z * ((b : ℝ) * n))) * ‖branchIntegral r b A z j n‖
    let P := (1 + (b : ℝ) * n) ^ (r - 1)
    ‖branchIntegral r 0 A z j n‖ ≤ P * x ∧
      x ≤ P * ‖branchIntegral r 0 A z j n‖ := by
  have hl := norm_branchIntegral_change_center_le hr hA 0 b z j n
  have hu := norm_branchIntegral_change_center_le hr hA b 0 z j n
  have hnm : ‖(b : ℂ) * n‖ = (b : ℝ) * n := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  simp only [Nat.cast_zero, zero_sub, sub_zero, neg_mul, norm_neg, hnm,
    mul_neg] at hl hu
  constructor
  · convert hl using 1
    ring
  · have h := mul_le_mul_of_nonneg_left hu (Real.exp_pos (-(Real.log z * ((b : ℝ) * n)))).le
    simp only [← mul_assoc] at h
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h
    simpa only [mul_assoc] using h

theorem logNorm_branchIntegral_recenter {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i)
    (b : ℕ) (z : ℝ) (j : ℤ) {n : ℕ} (hn : 1 ≤ n)
    (hI : 0 < ‖branchIntegral r 0 A z j n‖) :
    0 < ‖branchIntegral r b A z j n‖ ∧
      |Real.log ‖branchIntegral r b A z j n‖ -
        Real.log ‖branchIntegral r 0 A z j n‖ - Real.log z * ((b : ℝ) * n)| ≤
          (r - 1 : ℕ) * (Real.log (1 + (b : ℝ)) + Real.log (n : ℝ)) := by
  obtain ⟨hl, hu⟩ := norm_branchIntegral_recenter_bounds hr hA b z j n
  have hP : 0 < (1 + (b : ℝ) * n) ^ (r - 1) := by positivity
  obtain ⟨hx, hb⟩ := logarithmic_error_of_symmetric_comparison hI hP hl hu
  have hIm : 0 < ‖branchIntegral r b A z j n‖ := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hx
  rw [Real.log_mul (Real.exp_pos _).ne' hIm.ne', Real.log_exp, Real.log_pow] at hb
  have hbound : Real.log (1 + (b : ℝ) * n) ≤ Real.log (1 + (b : ℝ)) + Real.log (n : ℝ) := by
    rw [← Real.log_mul (by positivity : (1 + (b : ℝ)) ≠ 0)
      (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
    apply Real.log_le_log (by positivity)
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  refine ⟨hIm, ?_⟩
  have heq : -(Real.log z * ((b : ℝ) * n)) + Real.log ‖branchIntegral r b A z j n‖ -
      Real.log ‖branchIntegral r 0 A z j n‖ =
      Real.log ‖branchIntegral r b A z j n‖ - Real.log ‖branchIntegral r 0 A z j n‖ -
        Real.log z * ((b : ℝ) * n) := by ring
  rw [heq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _))

end ThisWork.HigherRank
