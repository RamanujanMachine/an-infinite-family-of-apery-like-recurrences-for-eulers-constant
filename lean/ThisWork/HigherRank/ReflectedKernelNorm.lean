module

public import ThisWork.HigherRank.ReflectedPhase
public import ThisWork.HigherRank.KernelNorm

/-! Logarithmic norms and positivity for the regular reflected kernel. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set

theorem reflectedPhase_eq_neg_limitingPhase (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (s : ℂ) :
    reflectedPhase r A z s = -limitingPhase r A z 0 (-s) := by
  unfold reflectedPhase reflectedLimitingEquation limitingPhase limitingEquation
  simp only [Int.cast_zero, mul_zero, add_zero]
  ring

theorem log_norm_reflectedKernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (n : ℕ) {x : ℂ} (hx : x.re < 1) :
    Real.log ‖reflectedKernel r m A z n x‖ = -(r : ℝ) * Real.log ‖Complex.Gamma (1 - x)‖ +
      (∑ i, Real.log ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖) +
      ((Real.log z : ℂ) * ((m : ℂ) * n - x)).re := by
  have h0 : ‖Complex.Gamma (1 - x)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.sub_re, Complex.one_re]; linarith))
  have hi (i : Fin (r - 1)) := norm_ne_zero_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (upper_re_pos_of_re_lt_one hA n hx i))
  have hp : (∏ i, ‖Complex.Gamma ((A i : ℂ) * n - x + 1)‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hi i)
  simp only [reflectedKernel, norm_mul, norm_pow, norm_inv, norm_prod, Complex.norm_exp]
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero r (inv_ne_zero h0)) hp) (Real.exp_ne_zero _),
    Real.log_mul (pow_ne_zero r (inv_ne_zero h0)) hp, Real.log_pow, Real.log_inv,
    Real.log_prod (fun i _ => hi i), Real.log_exp]
  ring

theorem reflectedKernel_ofReal {r : ℕ} (m : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) (t : ℝ) :
    reflectedKernel r m A z n (t : ℂ) =
      (((Real.Gamma (1 - t))⁻¹ ^ r * (∏ i, Real.Gamma (A i * n - t + 1)) *
        Real.exp (Real.log z * ((m : ℝ) * n - t)) : ℝ) : ℂ) := by
  simp only [reflectedKernel, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_prod, Complex.ofReal_exp, Complex.ofReal_sub,
    Complex.ofReal_natCast]
  simp only [← Complex.Gamma_ofReal]
  push_cast
  rfl

theorem reflectedKernel_real_pos {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (n : ℕ) {t : ℝ} (ht : t < 1) :
    0 < (reflectedKernel r m A z n (t : ℂ)).re := by
  rw [reflectedKernel_ofReal, Complex.ofReal_re]
  apply mul_pos
  · apply mul_pos
    · exact pow_pos (inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith))) _
    · apply Finset.prod_pos
      intro i _
      exact Real.Gamma_pos_of_pos (by nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n])
  · exact Real.exp_pos _

theorem log_norm_reflectedKernel_error {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ)
    {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : -s ∈ Complex.slitPlane)
    (hx : ((largeScale r n : ℂ) * s).re < 1) :
    Real.log ‖reflectedKernel r m A z n ((largeScale r n : ℂ) * s)‖ -
      Real.log (commonScale r m A z n) - largeScale r n * (reflectedPhase r A z s).re =
        -(r : ℝ) * Analytic.gammaNormError ((largeScale r n : ℂ) * (-s)) -
          (r : ℝ) * Real.log ‖(largeScale r n : ℂ) * (-s)‖ +
            ∑ i, rightGammaNormError r (A i) n s := by
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  let w : ℂ := (largeScale r n : ℂ) * (-s)
  have hwslit : w ∈ Complex.slitPlane := by
    apply (ThisWork.div_pos_real_mem_slitPlane_iff hR w).mp
    simpa only [w, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')] using hs
  have hw0 := Complex.slitPlane_ne_zero hwslit
  have hΓw := Complex.Gamma_ne_zero (Analytic.not_neg_nat_of_mem_slitPlane hwslit)
  have hlow : Real.log ‖Complex.Gamma (1 - (largeScale r n : ℂ) * s)‖ =
      Real.log ‖w‖ + Real.log ‖Complex.Gamma w‖ := by
    rw [show 1 - (largeScale r n : ℂ) * s = w + 1 by dsimp only [w]; ring,
      Complex.Gamma_add_one w hw0, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hw0) (norm_ne_zero_iff.mpr hΓw)]
  have hkernel := log_norm_reflectedKernel hA m z n hx
  have hscale := log_commonScale hA hz m n
  have hGammaScale := log_gammaScale hA n
  have hmain := congrArg Complex.re (scaled_stirlingMain_kernel hr hA z 0 hn (Complex.slitPlane_ne_zero hs))
  have hflip : limitingPhase r A z 0 (-s) = -reflectedPhase r A z s := by
    rw [reflectedPhase_eq_neg_limitingPhase, neg_neg]
  rw [hflip] at hmain
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum, Complex.im_sum,
    Int.cast_zero, Finset.sum_const_zero, mul_zero, zero_mul, sub_zero, add_zero] at hkernel hmain
  rw [hlow] at hkernel
  simp only [rightGammaNormError, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, mul_assoc, Analytic.gammaNormError]
  dsimp only [w] at hkernel
  nlinarith

end ThisWork.HigherRank
