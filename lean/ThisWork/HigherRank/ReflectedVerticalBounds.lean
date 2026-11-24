module

public import ThisWork.HigherRank.ReflectedKernelNorm
public import ThisWork.HigherRank.GammaVerticalBounds

/-! Fixed-height bank comparisons with the positive real reflected kernel. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set

noncomputable def gammaVerticalError (a h : ℝ) : ℝ :=
  Real.log ‖Complex.Gamma ((a : ℂ) + (h : ℂ) * Complex.I)‖ - Real.log ‖Complex.Gamma (a : ℂ)‖

theorem reflectedKernel_vertical_log_difference {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℝ} (hx : x < 1) (h : ℝ) :
    Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ -
      Real.log ‖reflectedKernel r b A z n (x : ℂ)‖ =
      -(r : ℝ) * gammaVerticalError (1 - x) (-h) + ∑ i, gammaVerticalError (A i * n - x + 1) (-h) := by
  rw [log_norm_reflectedKernel hA b z n (by simpa [Complex.mul_re] using hx),
    log_norm_reflectedKernel hA b z n (by simpa using hx)]
  have hlo : 1 - ((x : ℂ) + (h : ℂ) * Complex.I) =
      ((1 - x : ℝ) : ℂ) + ((-h : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hu (i : Fin (r - 1)) : (A i : ℂ) * n - ((x : ℂ) + (h : ℂ) * Complex.I) + 1 =
      ((A i * n - x + 1 : ℝ) : ℂ) + ((-h : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hu0 (i : Fin (r - 1)) : (A i : ℂ) * n - (x : ℂ) + 1 = ((A i * n - x + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hlo0 : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  simp_rw [hlo, hu, hu0, hlo0]
  simp only [gammaVerticalError, Finset.sum_sub_distrib, Complex.mul_re, Complex.sub_re,
    Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem abs_reflectedKernel_vertical_log_difference_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x h B : ℝ} (hx : x < 1) (hlo : |gammaVerticalError (1 - x) (-h)| ≤ B)
    (hu : ∀ i, |gammaVerticalError (A i * n - x + 1) (-h)| ≤ B) :
    |Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ -
      Real.log ‖reflectedKernel r b A z n (x : ℂ)‖| ≤ (2 * (r : ℝ) - 1) * B := by
  rw [reflectedKernel_vertical_log_difference hA b z n hx h]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hsum
  have habs := Finset.abs_sum_le_sum_abs (s := Finset.univ)
    (f := fun i => gammaVerticalError (A i * n - x + 1) (-h))
  have hadd := abs_add_le (-(r : ℝ) * gammaVerticalError (1 - x) (-h))
    (∑ i, gammaVerticalError (A i * n - x + 1) (-h))
  rw [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] at hadd
  nlinarith [mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem reflectedKernel_vertical_log_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ≤ 1 / 2) (h : ℝ) :
    |Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ -
      Real.log ‖reflectedKernel r b A z n (x : ℂ)‖| ≤
        (2 * (r : ℝ) - 1) * (|h| ^ 2 + 6 * |h|) := by
  apply abs_reflectedKernel_vertical_log_difference_le hr hA b z n (by linarith : x < 1)
  · simpa only [gammaVerticalError, abs_neg] using
      abs_log_norm_Gamma_vertical_sub_halfplane (b := -h) (by linarith : 1 / 2 ≤ 1 - x)
  · intro i
    simpa only [gammaVerticalError, abs_neg] using
      abs_log_norm_Gamma_vertical_sub_halfplane (b := -h)
        (by nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n] : 1 / 2 ≤ A i * n - x + 1)

theorem reflectedKernel_vertical_log_bound_far_left {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ≤ -1) (h : ℝ) :
    |Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ -
      Real.log ‖reflectedKernel r b A z n (x : ℂ)‖| ≤
        (2 * (r : ℝ) - 1) * (|h| ^ 2 + 2 * |h|) / (1 - x) := by
  rw [mul_div_assoc]
  apply abs_reflectedKernel_vertical_log_difference_le hr hA b z n (by linarith : x < 1)
  · simpa only [gammaVerticalError, abs_neg] using
      abs_log_norm_Gamma_vertical_sub_le (b := -h) (by linarith : 2 ≤ 1 - x)
  · intro i
    have ha : 2 ≤ A i * n - x + 1 := by nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n]
    have h := abs_log_norm_Gamma_vertical_sub_le (b := -h) ha
    simp only [abs_neg] at h
    apply h.trans
    exact div_le_div_of_nonneg_left (by positivity) (by linarith)
      (by nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n])

theorem abs_reflectedKernel_fixed_bank_log_le_one {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x h : ℝ} (hx : x ≤ -(6 * (r : ℝ))) (hh : |h| ≤ 1) :
    |Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ -
      Real.log ‖reflectedKernel r b A z n (x : ℂ)‖| ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hx1 : x ≤ -1 := by linarith
  have hb := reflectedKernel_vertical_log_bound_far_left hr hA b z n hx1 h
  have hfrac : (2 * (r : ℝ) - 1) * (|h| ^ 2 + 2 * |h|) / (1 - x) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1 - x)).mpr
    have hh2 : |h| ^ 2 ≤ 1 := by nlinarith [abs_nonneg h]
    nlinarith [mul_nonneg (show 0 ≤ 2 * (r : ℝ) - 1 by linarith)
      (show 0 ≤ 3 - (|h| ^ 2 + 2 * |h|) by linarith)]
  exact hb.trans hfrac

theorem norm_reflectedKernel_fixed_bank_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x h : ℝ} (hx : x ≤ -(6 * (r : ℝ))) (hh : |h| ≤ 1) :
    ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ ≤
      ‖reflectedKernel r b A z n (x : ℂ)‖ * Real.exp 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hlog := (abs_le.mp (abs_reflectedKernel_fixed_bank_log_le_one hr hA b z n hx hh)).2
  have hnz := reflectedKernel_ne_zero_of_re_lt_one hA b z n (x := (x : ℂ)) (by simpa using (show x < 1 by linarith))
  calc
    _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n (x : ℂ)‖ + 1) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr hnz)]

theorem norm_reflectedKernel_real_le_fixed_bank {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x h : ℝ} (hx : x ≤ -(6 * (r : ℝ))) (hh : |h| ≤ 1) :
    ‖reflectedKernel r b A z n (x : ℂ)‖ ≤
      ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ * Real.exp 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hlog := (abs_le.mp (abs_reflectedKernel_fixed_bank_log_le_one hr hA b z n hx hh)).1
  have hnz := reflectedKernel_ne_zero_of_re_lt_one hA b z n
    (x := (x : ℂ) + (h : ℂ) * Complex.I) (by simpa [Complex.mul_re] using (show x < 1 by linarith))
  calc
    _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n (x : ℂ)‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n ((x : ℂ) + (h : ℂ) * Complex.I)‖ + 1) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr hnz)]

end ThisWork.HigherRank
