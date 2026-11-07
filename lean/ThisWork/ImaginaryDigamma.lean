module

public import ThisWork.Argument
public import ThisWork.ScaledDigamma

/-! Digamma estimates controlled by distance from the real axis. -/

public section

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

theorem uniform_scaled_digamma_right_im {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, 0 ≤ s.re → η ≤ |s.im| →
      ‖Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / ε + 2)
  have hN₂ : 2 ≤ N := by
    exact_mod_cast (show (2 : ℝ) ≤ N by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hε])
  have hfirst : 1 / ((N : ℝ) - 1) ≤ ε / 2 := by
    apply (div_le_iff₀ (show 0 < (N : ℝ) - 1 by
      have h : (2 : ℝ) ≤ N := by exact_mod_cast hN₂
      linarith)).mpr
    nlinarith [(div_le_iff₀ hε).mp (show 2 / ε ≤ (N : ℝ) - 1 by linarith)]
  filter_upwards [eventually_ge_atTop (4 * (N : ℝ) / (η * ε)), eventually_ge_atTop (1 : ℝ)]
    with R hlarge hR₁
  refine ⟨by linarith, fun s hs him => ?_⟩
  have hden : R * η ≤ |((R : ℂ) * s).im| := by
    simpa [Complex.mul_im, abs_mul, abs_of_nonneg (show 0 ≤ R by linarith)] using
      mul_le_mul_of_nonneg_left him (show 0 ≤ R by linarith)
  have hsecond : 2 * (N : ℝ) / |((R : ℂ) * s).im| ≤ ε / 2 := by
    apply (div_le_iff₀ ((mul_pos (show 0 < R by linarith) hη).trans_le hden)).mpr
    nlinarith [(div_le_iff₀ (mul_pos hη hε)).mp hlarge,
      mul_le_mul_of_nonneg_right hden hε.le]
  exact (norm_digamma_sub_log_of_re_nonneg
    (by simpa [Complex.mul_re] using mul_nonneg (show 0 ≤ R by linarith) hs)
    (abs_pos.mp ((mul_pos (show 0 < R by linarith) hη).trans_le hden)) hN₂).trans (by linarith)

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

/-- Uniform convergence of the scaled digamma error on both sides of the
imaginary axis, away from the real axis. -/
theorem uniform_scaled_digamma_im {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, η ≤ |s.im| →
      ‖Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)‖ ≤ ε := by
  filter_upwards [uniform_scaled_digamma_right_im hη (half_pos hε),
    eventually_exp_decay_bounds (show 0 < 2 * Real.pi * η by positivity),
    eventually_ge_atTop (2 * (1 / η + 4 * Real.pi) / ε)] with R hright hdec hlarge
  refine ⟨hdec.1, fun s him => ?_⟩
  by_cases hre : 0 ≤ s.re
  · exact (hright.2 s hre him).trans (by linarith)
  have hA : ‖Complex.digamma (1 - (R : ℂ) * s) - Complex.log (1 - (R : ℂ) * s)‖ ≤ ε / 2 := by
    have h := hright.2 (((R⁻¹ : ℝ) : ℂ) - s)
      (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith [inv_pos.mpr hdec.1, lt_of_not_ge hre])
      (by simpa using him)
    rwa [show (R : ℂ) * (((R⁻¹ : ℝ) : ℂ) - s) = 1 - (R : ℂ) * s by
      rw [Complex.ofReal_inv, mul_sub, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hdec.1.ne')]] at h
  have hden : R * η ≤ |((R : ℂ) * s).im| := by
    simpa [Complex.mul_im, abs_mul, abs_of_pos hdec.1] using mul_le_mul_of_nonneg_left him hdec.1.le
  have he : Real.exp (-2 * Real.pi * |((R : ℂ) * s).im|) ≤ Real.exp (-(2 * Real.pi * η) * R) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 2 * Real.pi by positivity)]
  have hfrac : 1 / |((R : ℂ) * s).im| ≤ (1 / η) / R :=
    (one_div_le_one_div_of_le (mul_pos hdec.1 hη) hden).trans_eq (by field_simp)
  have hsmall : (1 / η + 4 * Real.pi) / R ≤ ε / 2 := by
    apply (div_le_iff₀ hdec.1).mpr
    nlinarith [(div_le_iff₀ hε).mp hlarge]
  have hb := norm_digamma_sub_log_reflection_im
    (abs_pos.mp ((mul_pos hdec.1 hη).trans_le hden)) (he.trans hdec.2.1)
  nlinarith [mul_le_mul_of_nonneg_left (he.trans hdec.2.2) (show 0 ≤ 4 * Real.pi by positivity),
    show (1 / η) / R + 4 * Real.pi * (1 / R) ≤ ε / 2 by convert hsmall using 1; ring]

theorem uniform_scaled_digamma_region {κ η ε : ℝ}
    (hκ : 0 < κ) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, κ ≤ s.re ∨ η ≤ |s.im| →
      ‖Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)‖ ≤ ε := by
  filter_upwards [uniform_scaled_digamma_right hκ, uniform_scaled_digamma_im hη hε,
    eventually_ge_atTop ((2 / κ) / ε)] with R hright him hlarge
  refine ⟨hright.1, fun s hs => hs.elim (fun hre => ?_) (fun h => him.2 s h)⟩
  exact (hright.2 s hre).trans ((div_le_iff₀ hright.1).mpr
    (by nlinarith [(div_le_iff₀ hε).mp hlarge]))

end ThisWork.Analytic
