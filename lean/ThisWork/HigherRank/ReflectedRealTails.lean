module

public import ThisWork.HigherRank.ReflectedSaddleEquation
public import ThisWork.HigherRank.ReflectedApproximation
public import ThisWork.HigherRank.IntegratedTails

/-! Uniform real-axis tail decay for the positive reflected kernel. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem uniform_re_reflectedEquation_real_lower {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      Real.log t - C ≤ (reflectedEquation r A z n (-(t : ℂ))).re := by
  let C := (∑ i, Real.log (A i + 2)) + 2 * (r : ℝ) + ((r : ℝ) - 1) + |Real.log z|
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  have hupper : ∀ᶠ n : ℕ in atTop, ∀ i, 4 ≤ A i * n :=
    Filter.eventually_all.mpr (fun i => (eventually_affine_conditions (by omega : 0 < r) (hA i) 0).mono
      (fun _ h => h.1))
  filter_upwards [hupper, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with n hupper hR hn t ht
  have hR0 : 0 < largeScale r n := zero_lt_one.trans_le hR
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hRn : largeScale r n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le
    (by exact_mod_cast hn) (by linarith [div_nonneg zero_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : 1 - 1 / (r : ℝ) ≤ 1)
  have hb := norm_digamma_add_one_sub_log_le
    (w := ((largeScale r n * t : ℝ) : ℂ)) (by simpa using mul_pos hR0 ht0)
  have he := (Complex.abs_re_le_norm _).trans hb
  simp only [Complex.sub_re, Complex.log_re, Complex.ofReal_re,
    Complex.norm_of_nonneg (mul_pos hR0 ht0).le, Real.log_mul hR0.ne' ht0.ne'] at he
  have hfrac : 2 / (largeScale r n * t) ≤ 2 :=
    (div_le_iff₀ (mul_pos hR0 ht0)).mpr (by nlinarith)
  have hleft : Real.log (largeScale r n) + Real.log t - 2 ≤
      (Complex.digamma (1 - (largeScale r n : ℂ) * (-(t : ℂ)))).re := by
    have hid : 1 - (largeScale r n : ℂ) * (-(t : ℂ)) = ((largeScale r n * t : ℝ) : ℂ) + 1 := by push_cast; ring
    rw [hid]
    linarith [(abs_le.mp he).1]
  have hu (i : Fin (r - 1)) := Analytic.re_digamma_right_tail_le (hA i).le hR0.le hRn hn ht
    (y := 0) (H := 0) (by norm_num) (hupper i)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, add_zero] at hu
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hlog := log_largeScale (by omega : 0 < r) (by omega : 0 < n)
  have hC := le_max_right 0 C
  simp only [reflectedEquation, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.re_sum, Complex.ofReal_re,
    zero_mul, sub_zero]
  dsimp only [C] at hC ⊢
  nlinarith [le_abs_self (Real.log z)]

theorem hasDerivAt_log_norm_reflectedKernel_left {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log ‖reflectedKernel r b A z n (-(R : ℂ) * (u : ℂ))‖)
      (-R * (logDeriv (reflectedKernel r b A z n) (-(R : ℂ) * (t : ℂ))).re) t := by
  have hγ : HasDerivAt (fun u : ℝ => -(R : ℂ) * (u : ℂ)) (-(R : ℂ)) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using ((hasDerivAt_id t).ofReal_comp).const_mul (-(R : ℂ))
  have hx : (-(R : ℂ) * (t : ℂ)).re < 1 := by simp only [Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]; nlinarith
  have h := Analytic.hasDerivAt_log_norm_comp (isOpen_lt Complex.continuous_re continuous_const)
    (fun x hx => (differentiableAt_reflectedKernel_of_re_lt_one hA b z n hx).differentiableWithinAt)
    (fun x hx => reflectedKernel_ne_zero_of_re_lt_one hA b z n hx) hγ hx
  simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, neg_mul] using h

theorem uniform_reflected_real_tail_decay {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a → ∀ t : ℝ, a ≤ t →
      ‖reflectedKernel r b A z n (-(largeScale r n : ℂ) * (t : ℂ))‖ ≤
        ‖reflectedKernel r b A z n (-(largeScale r n : ℂ) * (a : ℂ))‖ *
          Real.exp (-q * largeScale r n * (t - a)) := by
  obtain ⟨C, _, hb⟩ := uniform_re_reflectedEquation_real_lower hr hA z
  let T := Real.exp (C + q + 1) + 1
  have hT : 1 ≤ T := by dsimp only [T]; linarith [Real.exp_pos (C + q + 1)]
  refine ⟨T, hT, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 a ha t hat
  have ha1 := hT.trans ha
  have ht1 := ha1.trans hat
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hd (u : ℝ) (hu : 1 ≤ u) : HasDerivAt
      (fun v : ℝ => Real.log ‖reflectedKernel r b A z n (-(largeScale r n : ℂ) * (v : ℂ))‖)
      (-largeScale r n * (reflectedEquation r A z n (-(u : ℂ))).re) u := by
    have h := hasDerivAt_log_norm_reflectedKernel_left hA b z n hR (zero_lt_one.trans_le hu)
    rw [logDeriv_reflectedKernel_of_re_lt_one hA b z n
      (show (-(largeScale r n : ℂ) * (u : ℂ)).re < 1 by
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
          Complex.ofReal_im, neg_zero, zero_mul, sub_zero]; nlinarith)] at h
    simpa only [reflectedEquation, neg_mul, mul_neg] using h
  have hdiff := Analytic.log_decay_of_derivative_bound hd
    (fun u hu => mul_le_mul_of_nonpos_left (hn u hu) (neg_nonpos.mpr hR.le)) ha1 hat
  have hloga : C + q + 1 ≤ Real.log a := by
    have he : Real.exp (C + q + 1) ≤ a := by dsimp only [T] at ha; linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hlogt := Real.log_le_log (zero_lt_one.trans_le ha1) hat
  have hphase : q * (t - a) ≤ t * Real.log t - a * Real.log a - (C + 1) * (t - a) := by
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (sub_nonneg.mpr hlogt),
      mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hloga)]
  have hKa : 0 < ‖reflectedKernel r b A z n (-(largeScale r n : ℂ) * (a : ℂ))‖ :=
    norm_pos_iff.mpr (reflectedKernel_ne_zero_of_re_lt_one hA b z n (by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, neg_zero, zero_mul, sub_zero]; nlinarith))
  calc
    _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n (-(largeScale r n : ℂ) * (t : ℂ))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n (-(largeScale r n : ℂ) * (a : ℂ))‖ -
        q * largeScale r n * (t - a)) := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hphase hR.le])
    _ = _ := by rw [Real.exp_sub, Real.exp_log hKa, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring

end ThisWork.HigherRank
