module

public import ThisWork.HigherRank.ParabolicPhase
public import ThisWork.GammaNorm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Vertical Gamma comparisons for the fixed-height reflected Hankel banks. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Metric

theorem abs_im_digamma_right_le {a b : ℝ} (ha : 2 ≤ a) :
    |(Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I)).im| ≤ (|b| + 2) / a := by
  let w : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have ha0 : 0 < a := by linarith
  have herror : |(Complex.digamma w - Complex.log w).im| ≤ 2 / a := by
    exact (Complex.abs_im_le_norm _).trans (by
      simpa only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
          Analytic.norm_digamma_sub_log_le_two_div (s := w) (by simpa only [w, Complex.add_re,
            Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using ha))
  have harg : |Complex.arg w| ≤ |b| / a := by
    rw [show w = (a : ℂ) + (b : ℂ) * Complex.I from rfl, arg_right_halfplane ha0 b]
    simpa only [abs_div, abs_of_pos ha0] using (Real.abs_arctan_le_abs (x := b / a))
  have hsum := abs_add_le (Complex.digamma w - Complex.log w).im (Complex.log w).im
  simp only [Complex.sub_im, Complex.log_im] at herror
  simp only [Complex.sub_im, Complex.log_im, sub_add_cancel] at hsum
  change |(Complex.digamma w).im| ≤ _
  rw [add_div]
  linarith

theorem abs_log_norm_Gamma_vertical_sub_of_im_bound {a b K : ℝ} (ha : 0 < a)
    (hψ : ∀ u ∈ uIcc (0 : ℝ) b,
      |(Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)).im| ≤ K) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ -
      Real.log ‖Complex.Gamma (a : ℂ)‖| ≤ K * |b| := by
  have hd (u : ℝ) : HasDerivAt (fun t : ℝ => Real.log ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖)
      (Complex.I * Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)).re u := by
    apply Analytic.hasDerivAt_gammaLogNorm_comp
    · simpa only [id_eq, one_mul] using
        (((hasDerivAt_id (u : ℂ)).mul_const Complex.I).const_add (a : ℂ)).comp_ofReal
    · simpa using ha
  have hbound (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) b) :
      ‖(Complex.I * Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)).re‖ ≤ K := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, Real.norm_eq_abs, abs_neg]
    exact hψ u hu
  have h := (convex_uIcc (0 : ℝ) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) hbound left_mem_uIcc right_mem_uIcc
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero, Real.norm_eq_abs] using h

theorem abs_log_norm_Gamma_vertical_sub_le {a b : ℝ} (ha : 2 ≤ a) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ -
      Real.log ‖Complex.Gamma (a : ℂ)‖| ≤ (|b| ^ 2 + 2 * |b|) / a := by
  have hb (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) b) : |u| ≤ |b| := by
    rcases mem_uIcc.mp hu with hu | hu
    · simpa using abs_le_max_abs_abs hu.1 hu.2
    · simpa using abs_le_max_abs_abs hu.1 hu.2
  have h := abs_log_norm_Gamma_vertical_sub_of_im_bound (b := b) (K := (|b| + 2) / a) (by linarith : 0 < a)
    (fun u hu => (abs_im_digamma_right_le ha).trans
      ((div_le_div_iff_of_pos_right (by linarith)).mpr (by linarith [hb u hu])))
  convert h using 1
  ring

theorem abs_im_digamma_halfplane_le {a b : ℝ} (ha : 1 / 2 ≤ a) :
    |(Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I)).im| ≤ |b| + 6 := by
  let w : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have ha0 : 0 < a := by linarith
  have hw : w.re = a := by simp [w, Complex.mul_re]
  have hrec := Complex.digamma_apply_add_nat (s := w)
    (Analytic.not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by simpa only [hw] using ha0)))) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    add_zero, zero_add] at hrec
  have hinv (s : ℂ) (hs : a ≤ s.re) : |(s⁻¹).im| ≤ 2 := by
    have hnorm : a ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
    have hnorm0 : 0 < ‖s‖ := ha0.trans_le hnorm
    calc
      _ ≤ ‖s⁻¹‖ := Complex.abs_im_le_norm _
      _ = 1 / ‖s‖ := by rw [norm_inv, one_div]
      _ ≤ 2 := (div_le_iff₀ hnorm0).mpr (by linarith)
  have hw2 : w + 2 = ((a + 2 : ℝ) : ℂ) + (b : ℂ) * Complex.I := by dsimp only [w]; push_cast; ring
  have hshift : |(Complex.digamma (w + 2)).im| ≤ |b| + 2 := by
    rw [hw2]
    exact (abs_im_digamma_right_le (by linarith : 2 ≤ a + 2)).trans
      (div_le_self (by positivity) (by linarith : 1 ≤ a + 2))
  have hinv0 := hinv w (by rw [hw])
  have hinv1 := hinv (w + 1) (by simp only [Complex.add_re, Complex.one_re, hw]; linarith)
  have he : Complex.digamma w = Complex.digamma (w + 2) - w⁻¹ - (w + 1)⁻¹ := by
    linear_combination -hrec
  change |(Complex.digamma w).im| ≤ _
  rw [he, Complex.sub_im, Complex.sub_im]
  have h1 := abs_sub (Complex.digamma (w + 2)).im (w⁻¹).im
  have h2 := abs_sub ((Complex.digamma (w + 2)).im - (w⁻¹).im) ((w + 1)⁻¹).im
  linarith

theorem abs_log_norm_Gamma_vertical_sub_halfplane {a b : ℝ} (ha : 1 / 2 ≤ a) :
    |Real.log ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ -
      Real.log ‖Complex.Gamma (a : ℂ)‖| ≤ |b| ^ 2 + 6 * |b| := by
  have h := abs_log_norm_Gamma_vertical_sub_of_im_bound (by linarith : 0 < a)
    (K := |b| + 6) (fun u hu => by
      have hb : |u| ≤ |b| := by
        rcases mem_uIcc.mp hu with hu | hu
        · simpa using abs_le_max_abs_abs hu.1 hu.2
        · simpa using abs_le_max_abs_abs hu.1 hu.2
      exact (abs_im_digamma_halfplane_le ha).trans (by linarith))
  convert h using 1
  ring

end ThisWork.HigherRank
