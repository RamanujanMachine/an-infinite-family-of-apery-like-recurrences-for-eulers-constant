module

public import ThisWork.ReflectedApproximation

/-! The reflected limiting phase on the negative real saddle. Its real
restriction has a unique global maximum, with no logarithmic cut involved. -/

@[expose] public section
namespace ThisWork

open Set

noncomputable def reflectedPhase (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (s : ℂ) : ℂ :=
  s * (reflectedLimitingEquation r A z s - r)

noncomputable def reflectedRealPhase (c t : ℝ) : ℝ := t * (1 + Real.log (c / t))

theorem reflectedRealPhase_strict_max {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (hne : t ≠ c) :
    reflectedRealPhase c t < c := by
  have hct : c / t ≠ 1 := by intro he; exact hne ((div_eq_one_iff_eq ht.ne').mp he).symm
  have h := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos hc ht) hct) ht
  have hm : t * (c / t) = c := by field_simp
  unfold reflectedRealPhase
  nlinarith

theorem reflectedRealPhase_self {c : ℝ} (hc : 0 < c) : reflectedRealPhase c c = c := by
  simp [reflectedRealPhase, hc.ne']

theorem reflectedPhase_neg_real {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ} {z t : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (ht : 0 < t) :
    (reflectedPhase r A z (-(t : ℂ))).re = (r : ℝ) * reflectedRealPhase (saddleScale r A z) t := by
  have hc := saddleScale_pos hA hz
  have hlog := log_saddleScale hr hA hz
  unfold reflectedPhase reflectedLimitingEquation reflectedRealPhase
  rw [neg_neg, ← Complex.ofReal_log ht.le, Real.log_div hc.ne' ht.ne']
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, Complex.re_sum,
    mul_zero, zero_mul, sub_zero, neg_zero]
  nlinarith

theorem hasDerivAt_reflectedLimitingEquation (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    {s : ℂ} (hs : -s ∈ Complex.slitPlane) :
    HasDerivAt (reflectedLimitingEquation r A z) ((r : ℂ) / s) s := by
  have hlog := (Complex.hasDerivAt_log hs).comp s ((hasDerivAt_id s).neg)
  convert ((hlog.const_mul (r : ℂ)).sub_const (∑ i, (Real.log (A i) : ℂ))).sub_const (Real.log z : ℂ) using 1
  · rfl
  · simp only [neg_inv, mul_neg, neg_neg, mul_one, div_eq_mul_inv]

theorem hasDerivAt_reflectedPhase (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    {s : ℂ} (hs : -s ∈ Complex.slitPlane) :
    HasDerivAt (reflectedPhase r A z) (reflectedLimitingEquation r A z s) s := by
  have hs0 : s ≠ 0 := neg_ne_zero.mp (Complex.slitPlane_ne_zero hs)
  convert (hasDerivAt_id s).mul ((hasDerivAt_reflectedLimitingEquation r A z hs).sub_const (r : ℂ)) using 1
  · rfl
  · simp only [one_mul, id_eq, mul_div_cancel₀ _ hs0, sub_add_cancel]

theorem reflectedLimitingEquation_saddle {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    reflectedLimitingEquation r A z (-(saddleScale r A z : ℂ)) = 0 := by
  have hc := saddleScale_pos hA hz
  have hlog : (r : ℂ) * (Real.log (saddleScale r A z) : ℂ) =
      (∑ i, (Real.log (A i) : ℂ)) + (Real.log z : ℂ) := by
    exact_mod_cast log_saddleScale hr hA hz
  unfold reflectedLimitingEquation
  rw [neg_neg, ← Complex.ofReal_log hc.le]
  linear_combination hlog

theorem reflectedPhase_saddle {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    reflectedPhase r A z (-(saddleScale r A z : ℂ)) = (r : ℂ) * saddleScale r A z := by
  rw [reflectedPhase, reflectedLimitingEquation_saddle hr hA hz]
  ring

end ThisWork
