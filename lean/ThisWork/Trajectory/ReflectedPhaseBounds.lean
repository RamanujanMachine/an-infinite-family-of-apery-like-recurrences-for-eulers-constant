module
public import ThisWork.Trajectory.BranchPhaseComparison
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
/-! The real maximum of the reflected square-root phase and its horizontal bounds. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

noncomputable def reflectedRealPhase (c t : ℝ) : ℝ := 2 * (t - t * Real.log (t / c))

theorem reflectedRealPhase_le {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    reflectedRealPhase c t ≤ 2 * c := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [reflectedRealPhase, zero_mul, mul_zero, sub_zero]
    positivity
  · have h := Real.log_le_sub_one_of_pos (div_pos hc ht)
    rw [Real.log_div hc.ne' ht.ne'] at h
    have hmul := (mul_le_mul_of_nonneg_left h ht.le)
    simp only [mul_sub, mul_div_cancel₀ c ht.ne', mul_one] at hmul
    rw [reflectedRealPhase, Real.log_div ht.ne' hc.ne']
    nlinarith

theorem reflectedRealPhase_lt {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hne : t ≠ c) :
    reflectedRealPhase c t < 2 * c := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [reflectedRealPhase, zero_mul, mul_zero, sub_zero]
    positivity
  · have h := Real.log_lt_sub_one_of_pos (div_pos hc ht) (by
      intro h; exact hne (div_eq_one_iff_eq ht.ne' |>.mp h).symm)
    rw [Real.log_div hc.ne' ht.ne'] at h
    have hmul := (mul_lt_mul_of_pos_left h ht)
    simp only [mul_sub, mul_div_cancel₀ c ht.ne', mul_one] at hmul
    rw [reflectedRealPhase, Real.log_div ht.ne' hc.ne']
    nlinarith

theorem continuous_reflectedRealPhase {c : ℝ} (hc : 0 < c) :
    Continuous (reflectedRealPhase c) := by
  have he : reflectedRealPhase c = (fun t => 2 * (t - t * Real.log t + t * Real.log c)) := by
    funext t
    by_cases ht : t = 0
    · simp only [ht, reflectedRealPhase, zero_mul, sub_zero, zero_add]
    · rw [reflectedRealPhase, Real.log_div ht hc.ne']
      ring
  rw [he]
  exact continuous_const.mul ((continuous_id.sub Real.continuous_mul_log).add
    (continuous_id.mul continuous_const))

theorem sqrtPhase_eq_log {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : s ≠ 0) :
    sqrtPhase c s = 2 * s * (Complex.log s - (Real.log c : ℂ) - 1) := by
  have hdiv : Complex.log (s / (c : ℂ)) = Complex.log s - (Real.log c : ℂ) := by
    rw [show s / (c : ℂ) = ((c⁻¹ : ℝ) : ℂ) * s by push_cast; ring,
      Complex.log_ofReal_mul (inv_pos.mpr hc) hs, Real.log_inv, Complex.ofReal_neg]
    ring
  simp only [sqrtPhase, limitingPhase, limitingEquation, twist_three, add_zero, hdiv]
  ring

theorem re_sqrtBranchPhase_one_neg {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.im) :
    (sqrtBranchPhase .one c (-s)).re = -(sqrtPhase c s).re := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hs; linarith
  rw [sqrtBranchPhase, sqrtPhase_eq_log hc (neg_ne_zero.mpr hs0), sqrtPhase_eq_log hc hs0]
  simp only [twist_one, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.log_re, Complex.log_im, norm_neg,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hs, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
    mul_zero, mul_one, add_zero, sub_zero]
  norm_num
  ring

/-- Above the positive real axis, imaginary displacement costs at most `pi*y`
relative to the real reflected phase. -/
theorem neg_re_sqrtPhase_le_realPhase {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hr : 0 ≤ s.re) (hi : 0 < s.im) :
    -(sqrtPhase c s).re ≤ reflectedRealPhase c s.re + Real.pi * s.im := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hi; linarith
  rw [sqrtPhase_eq_log hc hs0]
  have harg := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hr : 0 ≤ s.re ∨ s.im < 0)
  have hlog : s.re * Real.log s.re ≤ s.re * Real.log ‖s‖ := by
    rcases hr.eq_or_lt with h | h
    · simp only [← h, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (Complex.re_le_norm s)) h.le
  have he : reflectedRealPhase c s.re = 2 * (s.re - s.re * Real.log s.re + s.re * Real.log c) := by
    by_cases h : s.re = 0
    · simp only [reflectedRealPhase, h, zero_mul, sub_zero, zero_add]
    · rw [reflectedRealPhase, Real.log_div h hc.ne']
      ring
  simp only [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, sub_zero] at ⊢
  norm_num
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right harg hi.le]

/-- A uniform strict gap away from the unique real growing saddle. -/
theorem reflectedRealPhase_compact_gap {c δ T : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ t ∈ Icc (0 : ℝ) T, δ ≤ |t - c| → reflectedRealPhase c t ≤ 2 * c - ε := by
  let K : Set ℝ := Icc 0 T ∩ {t | δ ≤ |t - c|}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).abs))
  by_cases hne : K.Nonempty
  · obtain ⟨t₀, ht₀, hmax⟩ := hK.exists_isMaxOn hne (continuous_reflectedRealPhase hc).continuousOn
    have hlt : reflectedRealPhase c t₀ < 2 * c := reflectedRealPhase_lt hc ht₀.1.1 (by
      intro h
      have hg : δ ≤ |t₀ - c| := ht₀.2
      rw [h, sub_self, abs_zero] at hg
      linarith)
    refine ⟨2 * c - reflectedRealPhase c t₀, sub_pos.mpr hlt, fun t ht hg => ?_⟩
    have hb : reflectedRealPhase c t ≤ reflectedRealPhase c t₀ := hmax (show t ∈ K from ⟨ht, hg⟩)
    linarith
  · refine ⟨1, zero_lt_one, fun t ht hg => ?_⟩
    exact (hne ⟨t, ht, hg⟩).elim

/-- On the short part to the right of the origin, the reflected phase is
small; the growing maximum occurs on the negative side of the original contour. -/
theorem neg_re_sqrtPhase_le_of_re_nonpos {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hr : s.re ≤ 0) (hi : 0 < s.im) (hn : ‖s‖ ≤ 2 * c) :
    -(sqrtPhase c s).re ≤ 2 * Real.pi * s.im := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_im] at hi; linarith
  have hlog : Real.log ‖s‖ - Real.log c ≤ 1 := by
    have h := Real.log_le_log (norm_pos_iff.mpr hs0) hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hc.ne'] at h
    have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [sqrtPhase_eq_log hc hs0]
  simp only [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, sub_zero]
  norm_num
  nlinarith [mul_nonneg (neg_nonneg.mpr hr) (by linarith : 0 ≤ 1 - (Real.log ‖s‖ - Real.log c)),
    mul_le_mul_of_nonneg_right (Complex.arg_le_pi s) hi.le]

theorem re_sqrtPhase_log {c : ℝ} (hc : 0 < c) (s : ℂ) :
    (sqrtPhase c s).re = 2 * (s.re * (Real.log ‖s‖ - Real.log c - 1) - s.im * s.arg) := by
  by_cases hs : s = 0
  · simp [hs, sqrtPhase, limitingPhase]
  · rw [sqrtPhase_eq_log hc hs]
    simp only [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.sub_re, Complex.sub_im, sub_zero]
    norm_num
    ring

theorem neg_re_sqrtPhase_le_realPhase_abs {c : ℝ} (hc : 0 < c) (s : ℂ) (hr : 0 ≤ s.re) :
    -(sqrtPhase c s).re ≤ reflectedRealPhase c s.re + Real.pi * |s.im| := by
  have hlog : s.re * Real.log s.re ≤ s.re * Real.log ‖s‖ := by
    rcases hr.eq_or_lt with h | h
    · simp only [← h, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (Complex.re_le_norm s)) h.le
  have he : reflectedRealPhase c s.re = 2 * (s.re - s.re * Real.log s.re + s.re * Real.log c) := by
    by_cases h : s.re = 0
    · simp only [reflectedRealPhase, h, zero_mul, sub_zero, zero_add]
    · rw [reflectedRealPhase, Real.log_div h hc.ne']
      ring
  have harg := (Complex.abs_arg_le_pi_div_two_iff.mpr hr)
  have hprod : s.im * s.arg ≤ |s.im| * (Real.pi / 2) := by
    calc
      _ ≤ |s.im * s.arg| := le_abs_self _
      _ = |s.im| * |s.arg| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left harg (abs_nonneg _)
  rw [re_sqrtPhase_log hc, he]
  nlinarith

theorem neg_re_sqrtPhase_le_of_re_nonpos_abs {c : ℝ} (hc : 0 < c) (s : ℂ)
    (hr : s.re ≤ 0) (hn : ‖s‖ ≤ 2 * c) :
    -(sqrtPhase c s).re ≤ 2 * Real.pi * |s.im| := by
  by_cases hs0 : s = 0
  · simp [hs0, sqrtPhase, limitingPhase]
  have hlog : Real.log ‖s‖ - Real.log c ≤ 1 := by
    have h := Real.log_le_log (norm_pos_iff.mpr hs0) hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hc.ne'] at h
    have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hprod : s.im * s.arg ≤ |s.im| * Real.pi := by
    calc
      _ ≤ |s.im * s.arg| := le_abs_self _
      _ = |s.im| * |s.arg| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi s) (abs_nonneg _)
  rw [re_sqrtPhase_log hc]
  nlinarith [mul_nonneg (neg_nonneg.mpr hr) (by linarith : 0 ≤ 1 - (Real.log ‖s‖ - Real.log c))]

/-- The full horizontal reflected phase has only a linear height loss. -/
theorem neg_re_sqrtPhase_horizontal_bound {c η : ℝ} (hc : 0 < c) (hη : η ≤ c)
    (hπη : Real.pi * η ≤ c) {s : ℂ} (hr : -c ≤ s.re) (hi : |s.im| ≤ η) :
    -(sqrtPhase c s).re ≤ 2 * c + Real.pi * η := by
  by_cases hs : 0 ≤ s.re
  · exact (neg_re_sqrtPhase_le_realPhase_abs hc s hs).trans (by
      nlinarith [reflectedRealPhase_le hc hs, mul_le_mul_of_nonneg_left hi Real.pi_pos.le])
  · have hs' : s.re ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have hn : ‖s‖ ≤ 2 * c := (Complex.norm_le_abs_re_add_abs_im s).trans (by
      rw [abs_of_nonpos hs']
      linarith)
    exact (neg_re_sqrtPhase_le_of_re_nonpos_abs hc s hs' hn).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le])

theorem reflectedRealPhase_eq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    reflectedRealPhase c t = 2 * (t - t * Real.log t + t * Real.log c) := by
  by_cases h : t = 0
  · simp [h, reflectedRealPhase]
  rw [reflectedRealPhase, Real.log_div h hc.ne']
  ring

theorem hasDerivAt_reflectedRealPhase {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (reflectedRealPhase c) (-2 * Real.log (t / c)) t := by
  have h := (((hasDerivAt_id t).sub (Real.hasDerivAt_mul_log ht.ne')).add
    ((hasDerivAt_id t).mul_const (Real.log c))).const_mul 2
  simp only [Pi.sub_apply, Pi.add_apply, id_eq, one_mul] at h
  change HasDerivAt (fun u => 2 * (u - u * Real.log u + u * Real.log c))
    (2 * (1 - (Real.log t + 1) + Real.log c)) t at h
  have he : (fun u => 2 * (u - u * Real.log u + u * Real.log c)) = reflectedRealPhase c :=
    funext (fun u => (reflectedRealPhase_eq hc u).symm)
  rw [he] at h
  convert h using 1
  rw [Real.log_div ht.ne' hc.ne']
  ring

theorem reflectedRealPhase_antitone {c : ℝ} (hc : 0 < c) :
    AntitoneOn (reflectedRealPhase c) (Ici c) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => -2 * Real.log (t / c))
    (convex_Ici c) (continuous_reflectedRealPhase hc).continuousOn
  · intro t ht
    rw [interior_Ici] at ht
    exact (hasDerivAt_reflectedRealPhase hc (hc.trans ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hct : c < t := ht
    have hlog : 0 ≤ Real.log (t / c) := Real.log_nonneg ((le_div_iff₀ hc).mpr (by linarith))
    linarith

theorem reflectedRealPhase_global_gap {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → δ ≤ |t - c| → reflectedRealPhase c t ≤ 2 * c - ε := by
  obtain ⟨ε, hε, hb⟩ := reflectedRealPhase_compact_gap (T := 2 * c) hc (lt_min hδ hc)
  refine ⟨ε, hε, fun t ht hd => ?_⟩
  by_cases htc : t ≤ 2 * c
  · exact hb t ⟨ht, htc⟩ ((min_le_left δ c).trans hd)
  · have htwo : reflectedRealPhase c (2 * c) ≤ 2 * c - ε :=
      hb (2 * c) ⟨by positivity, le_rfl⟩ (by
        rw [show 2 * c - c = c by ring, abs_of_pos hc]
        exact min_le_right _ _)
    exact (reflectedRealPhase_antitone hc (by change c ≤ 2 * c; linarith)
      (by change c ≤ t; linarith) (by linarith : 2 * c ≤ t)).trans htwo

/-- A single fixed positive contour height works uniformly away from the
negative saddle; no contour approaches the Gamma poles as `n` grows. -/
theorem reflectedPhase_horizontal_gap {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ η > 0, η ≤ c ∧ Real.pi * η ≤ c / 4 ∧ ∃ ε > 0,
      ∀ s : ℂ, -c ≤ s.re → |s.im| ≤ η → δ ≤ |s.re - c| →
        -(sqrtPhase c s).re ≤ 2 * c - ε := by
  obtain ⟨q, hq, hgap⟩ := reflectedRealPhase_global_gap hc hδ
  let η := min c (min (c / (4 * Real.pi)) (q / (4 * Real.pi)))
  have hη : 0 < η := lt_min hc (lt_min (by positivity) (by positivity))
  have hηc : η ≤ c := min_le_left _ _
  have hηπ : Real.pi * η ≤ c / 4 := by
    have h := (min_le_right c _).trans (min_le_left (c / (4 * Real.pi)) (q / (4 * Real.pi)))
    dsimp only [η] at ⊢
    nlinarith [(le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp h]
  have hηq : Real.pi * η ≤ q / 4 := by
    have h := (min_le_right c _).trans (min_le_right (c / (4 * Real.pi)) (q / (4 * Real.pi)))
    nlinarith [(le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp h]
  refine ⟨η, hη, hηc, hηπ, min c (q / 2), lt_min hc (half_pos hq), fun s hr hi hd => ?_⟩
  by_cases hs : 0 ≤ s.re
  · have hg := hgap s.re hs hd
    have hb := neg_re_sqrtPhase_le_realPhase_abs hc s hs
    nlinarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le, min_le_right c (q / 2)]
  · have hs' : s.re ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have hn : ‖s‖ ≤ 2 * c := (Complex.norm_le_abs_re_add_abs_im s).trans (by
      rw [abs_of_nonpos hs']
      linarith)
    have hb := neg_re_sqrtPhase_le_of_re_nonpos_abs hc s hs' hn
    nlinarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le, min_le_left c (q / 2)]

end ThisWork.Trajectory
