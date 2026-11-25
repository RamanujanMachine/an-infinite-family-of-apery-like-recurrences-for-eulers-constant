module

public import ThisWork.ScaledDigamma

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology

theorem hasDerivAt_log_add_real_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (z + (u : ℂ))) (z + (t : ℂ))⁻¹ t := by
  have h := (Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr
    (Or.inr (show (z + (t : ℂ)).im ≠ 0 by simpa using him)))).comp
    (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_add z)
  simpa only [Function.comp_def, id_eq, mul_one] using h.comp_ofReal

theorem norm_resolvent_add_real_le_im {z : ℂ} (him : z.im ≠ 0) (t : ℝ) :
    ‖(z + (t : ℂ))⁻¹‖ ≤ 1 / |z.im| := by
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (abs_pos.mpr him)
    (by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using
      Complex.abs_im_le_norm (z + (t : ℂ)))

theorem norm_log_add_real_sub_le_im {z : ℂ} (him : z.im ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.log (z + (a : ℂ)) - Complex.log z‖ ≤ a / |z.im| := by
  have h := (convex_Icc (0 : ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hasDerivAt_log_add_real_of_im_ne_zero him u).hasDerivWithinAt)
    (fun u _ => norm_resolvent_add_real_le_im him u) (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha)
  simpa only [Complex.ofReal_zero, add_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg ha, div_mul_eq_mul_div, one_mul] using h

theorem norm_digamma_add_nat_sub_le_im {z : ℂ} (him : z.im ≠ 0) (N : ℕ) :
    ‖Complex.digamma (z + (N : ℂ)) - Complex.digamma z‖ ≤ (N : ℝ) / |z.im| := by
  rw [Complex.digamma_apply_add_nat (fun m he => him (by
    simp only [he, Complex.neg_im, Complex.natCast_im, neg_zero])), add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖(z + (k : ℂ))⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, 1 / |z.im| := Finset.sum_le_sum (fun k _ =>
      by simpa only [Complex.ofReal_natCast] using norm_resolvent_add_real_le_im him (k : ℝ))
    _ = _ := by simp [div_eq_mul_inv]

theorem norm_digamma_sub_log_of_re_nonneg {z : ℂ} (hre : 0 ≤ z.re) (him : z.im ≠ 0)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖Complex.digamma z - Complex.log z‖ ≤ 1 / ((N : ℝ) - 1) + 2 * N / |z.im| := by
  have hN₀ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hright : ‖Complex.digamma (z + (N : ℂ)) - Complex.log (z + (N : ℂ))‖ ≤ 1 / ((N : ℝ) - 1) :=
    (norm_digamma_sub_log_le (by simpa only [Complex.add_re, Complex.natCast_re] using
      (show 1 < z.re + (N : ℝ) by linarith))).trans
      (one_div_le_one_div_of_le (by linarith : 0 < (N : ℝ) - 1)
        (by simpa only [Complex.add_re, Complex.natCast_re] using (show (N : ℝ) - 1 ≤ z.re + N - 1 by linarith)))
  calc
    _ = ‖(Complex.digamma z - Complex.digamma (z + (N : ℂ))) +
        (Complex.digamma (z + (N : ℂ)) - Complex.log (z + (N : ℂ))) +
        (Complex.log (z + (N : ℂ)) - Complex.log z)‖ := by congr 1; ring
    _ ≤ (‖Complex.digamma z - Complex.digamma (z + (N : ℂ))‖ +
        ‖Complex.digamma (z + (N : ℂ)) - Complex.log (z + (N : ℂ))‖) +
        ‖Complex.log (z + (N : ℂ)) - Complex.log z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ((N : ℝ) / |z.im| + 1 / ((N : ℝ) - 1)) + (N : ℝ) / |z.im| :=
      add_le_add (add_le_add (by simpa only [norm_sub_rev] using norm_digamma_add_nat_sub_le_im him N) hright)
        (by simpa only [Complex.ofReal_natCast] using norm_log_add_real_sub_le_im him (a := (N : ℝ)) (Nat.cast_nonneg N))
    _ = _ := by ring

theorem norm_digamma_sub_log_reflection_im {z : ℂ} (him : z.im ≠ 0)
    (hexp : Real.exp (-2 * Real.pi * |z.im|) ≤ 1 / 2) :
    ‖Complex.digamma z - Complex.log z‖ ≤
      ‖Complex.digamma (1 - z) - Complex.log (1 - z)‖ + 1 / |z.im| +
        4 * Real.pi * Real.exp (-2 * Real.pi * |z.im|) := by
  have hcorr : ∃ C : ℂ, ‖C‖ ≤ 4 * Real.exp (-2 * Real.pi * |z.im|) ∧
      Complex.digamma z - Complex.log z =
        (Complex.digamma (1 - z) - Complex.log (1 - z)) +
        (Complex.log (1 - z) - Complex.log (-z)) - (Real.pi : ℂ) * C := by
    rcases lt_or_gt_of_ne him with hneg | hpos
    · refine ⟨Complex.cot ((Real.pi : ℂ) * z) - Complex.I, ?_, ?_⟩
      · have he : -2 * Real.pi * |z.im| = 2 * Real.pi * z.im := by rw [abs_of_neg hneg]; ring
        rw [he] at hexp ⊢
        exact norm_cot_pi_sub_I_le hexp
      · rw [digamma_reflection_of_im_ne_zero him, log_neg_of_im_neg hneg]
        ring
    · refine ⟨Complex.cot ((Real.pi : ℂ) * z) + Complex.I, ?_, ?_⟩
      · rw [abs_of_pos hpos] at hexp ⊢
        exact norm_cot_pi_add_I_le hexp
      · rw [digamma_reflection_of_im_ne_zero him, log_neg_of_im_pos hpos]
        ring
  have hB : ‖Complex.log (1 - z) - Complex.log (-z)‖ ≤ 1 / |z.im| := by
    simpa only [Complex.ofReal_one, neg_add_eq_sub, Complex.neg_im, abs_neg] using
      norm_log_add_real_sub_le_im (z := -z) (by simpa only [Complex.neg_im] using neg_ne_zero.mpr him)
        (a := 1) zero_le_one
  obtain ⟨C, hC, he⟩ := hcorr
  calc
    _ = ‖(Complex.digamma (1 - z) - Complex.log (1 - z)) +
        (Complex.log (1 - z) - Complex.log (-z)) - (Real.pi : ℂ) * C‖ := congrArg norm he
    _ ≤ (‖Complex.digamma (1 - z) - Complex.log (1 - z)‖ +
        ‖Complex.log (1 - z) - Complex.log (-z)‖) + ‖(Real.pi : ℂ) * C‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ (‖Complex.digamma (1 - z) - Complex.log (1 - z)‖ + 1 / |z.im|) +
        Real.pi * (4 * Real.exp (-2 * Real.pi * |z.im|)) :=
      add_le_add (add_le_add (le_refl _) hB) (by
        rw [norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
        exact mul_le_mul_of_nonneg_left hC Real.pi_pos.le)
    _ = _ := by ring

end ThisWork.Analytic
