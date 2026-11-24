module

public import ThisWork.HigherRank.AnchorNorm
public import ThisWork.HigherRank.ParabolicKernelApproximation

/-! Transfer of the positive real normalization to translated parabolic
arcs by integration of the exact saddle equation. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_kernelPhaseError_positive_translation {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {q : ℝ} (hq : 0 < q)
    (b : ℕ) (z : ℝ) (j : ℤ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ ≤ q / 8 →
      |kernelPhaseError r b A z j n ((q : ℂ) + δ) - kernelPhaseError r b A z j n q| ≤
        C * (largeScale r n * smallParameter r n) := by
  obtain ⟨C, hC, he⟩ := uniform_exactSaddleEquation_region hr hA z j
    (by positivity : 0 < q / 2) zero_lt_one (by positivity : 0 ≤ 2 * q)
  refine ⟨C * q / 8, by positivity, ?_⟩
  filter_upwards [he, eventually_scaled_slit_in_kernelDomain (by omega : 0 < r) hA (2 * q),
    eventually_gt_atTop (0 : ℕ)] with n hn hdom hn0 δ hδ
  have hgeom (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      ‖(q : ℂ) + (t : ℂ) * δ‖ ≤ 2 * q ∧ q / 2 ≤ ((q : ℂ) + (t : ℂ) * δ).re := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hmul : ‖(t : ℂ) * δ‖ ≤ ‖δ‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht'.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht'.2
    have hnorm := norm_add_le (q : ℂ) ((t : ℂ) * δ)
    rw [Complex.norm_of_nonneg hq.le] at hnorm
    have hre := (Complex.abs_re_le_norm ((t : ℂ) * δ)).trans hmul
    rw [Complex.add_re, Complex.ofReal_re]
    exact ⟨by linarith, by linarith [(neg_le_abs ((t : ℂ) * δ).re)]⟩
  have hslit (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : (q : ℂ) + (t : ℂ) * δ ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl ((half_pos hq).trans_le (hgeom t ht).2))
  have hγ (t : ℝ) : HasDerivAt (fun u : ℝ => (q : ℂ) + (u : ℂ) * δ) δ t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt.mul_const δ).const_add (q : ℂ)
  have h := kernelPhaseError_curve_bound (b := b) hn0 (fun t _ => hγ t) (fun _ _ => le_rfl) hslit
    (fun t ht => hdom _ ((Complex.re_le_norm _).trans (hgeom t ht).1) (hslit t ht))
    (fun t ht => hn _ (hgeom t ht).1 (Or.inl (hgeom t ht).2))
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero,
    sub_zero, abs_one, mul_one] at h
  have hR : 0 ≤ largeScale r n := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _).le
  have hε : 0 ≤ smallParameter r n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  nlinarith [mul_le_mul_of_nonneg_left hδ (mul_nonneg (mul_nonneg hR hC) hε)]

theorem uniform_log_norm_kernel_parabola {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (j : ℤ) {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ ≤ a ^ 2 / 8 → ∀ auxB : ℝ, |auxB| ≤ B →
      |Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB))‖ -
        Real.log (commonScale r b A z n) - largeScale r n * (limitingPhase r A z j (δ + parabolicPoint a auxB)).re| ≤
          C * (largeScale r n * smallParameter r n) := by
  have hq : 0 < a ^ 2 := sq_pos_of_pos ha
  obtain ⟨Ca, hCa, hanchor⟩ := uniform_log_norm_kernel_positive_anchor hr hA hz hq b j
  obtain ⟨Ct, hCt, htranslate⟩ := uniform_kernelPhaseError_positive_translation hr hA hq b z j
  obtain ⟨Cp, hCp, hparabola⟩ := uniform_kernelPhaseError_parabola hr hA b z j ha hB
  refine ⟨Cp * B + Ct + Ca, by positivity, ?_⟩
  filter_upwards [hanchor, htranslate, hparabola, eventually_gt_atTop (0 : ℕ)]
    with n hnA hnT hnP hn0 δ hδ auxB hb
  have hp0 : parabolicPoint a 0 = ((a ^ 2 : ℝ) : ℂ) := by simp [parabolicPoint]
  have hP := hnP δ hδ 0 auxB (by simpa using hB) hb
  rw [hp0, add_comm δ ((a ^ 2 : ℝ) : ℂ)] at hP
  simp only [sub_zero] at hP
  have hT := hnT δ hδ
  have hA' : |kernelPhaseError r b A z j n (a ^ 2 : ℝ) - Real.log (commonScale r b A z n)| ≤
      Ca * (largeScale r n * smallParameter r n) := by
    convert hnA using 1
    congr 1
    unfold kernelPhaseError
    ring
  have hR : 0 ≤ largeScale r n := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _).le
  have hε : 0 ≤ smallParameter r n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hlen := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hR hCp) hε)
  have hbound : |kernelPhaseError r b A z j n (δ + parabolicPoint a auxB) -
      Real.log (commonScale r b A z n)| ≤ (Cp * B + Ct + Ca) * (largeScale r n * smallParameter r n) := by
    exact abs_le.mpr ⟨by nlinarith [(abs_le.mp hP).1, (abs_le.mp hT).1, (abs_le.mp hA').1],
      by nlinarith [(abs_le.mp hP).2, (abs_le.mp hT).2, (abs_le.mp hA').2]⟩
  convert hbound using 1
  congr 1
  unfold kernelPhaseError
  ring

end ThisWork.HigherRank
