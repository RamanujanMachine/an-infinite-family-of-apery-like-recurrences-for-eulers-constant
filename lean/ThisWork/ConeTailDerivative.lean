module

public import ThisWork.SaddleEquation
public import ThisWork.DigammaTailTools

/-! Tail derivative bounds uniform in growing contour heights. The cone
`|Im s| ≤ -Re s` contains the endpoints of every sufficiently long parabola. -/

@[expose] public section
namespace ThisWork

open Set Filter
open scoped Topology

theorem norm_right_factor_cone_le {α R t y : ℝ} {n : ℕ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hRn : R ≤ n) (hn : 1 ≤ n)
    (ht : 1 ≤ t) (hy : |y| ≤ t) :
    ‖(α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ ≤
      (n : ℝ) * (α + 3) * t := by
  rw [show (α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1 =
    ((α * n + R * t + 1 : ℝ) : ℂ) + ((-R * y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  calc
    _ ≤ ‖((α * n + R * t + 1 : ℝ) : ℂ)‖ + ‖((-R * y : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = α * n + R * t + 1 + R * |y| := by
      rw [Complex.norm_of_nonneg (show 0 ≤ α * n + R * t + 1 by positivity)]
      simp [abs_of_nonneg hR]
    _ ≤ _ := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnt : 1 ≤ (n : ℝ) * t := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy hR,
        mul_le_mul_of_nonneg_right hRn (show 0 ≤ t by linarith),
        mul_nonneg (mul_nonneg hα (Nat.cast_nonneg (α := ℝ) n)) (show 0 ≤ t - 1 by linarith)]

theorem re_digamma_right_cone_le {α R t y : ℝ} {n : ℕ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hRn : R ≤ n) (hn : 1 ≤ n)
    (ht : 1 ≤ t) (hy : |y| ≤ t) (hA : 4 ≤ α * n) :
    (Complex.digamma ((α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1)).re ≤
      Real.log (n : ℝ) + Real.log (α + 3) + Real.log t + 1 := by
  have hz : 2 ≤ ((α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, Complex.neg_re,
      Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
    nlinarith [mul_nonneg hR (show 0 ≤ t by linarith)]
  have hl := Real.log_le_log
    (show 0 < ‖(α : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ from
      (show (0 : ℝ) < 2 by norm_num).trans_le (hz.trans (Complex.re_le_norm _)))
    (norm_right_factor_cone_le hα hR hRn hn ht hy)
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul (mul_pos hn₀ (show 0 < α + 3 by positivity)).ne'
    (show t ≠ 0 by linarith), Real.log_mul hn₀.ne' (show α + 3 ≠ 0 by positivity)] at hl
  linarith [Analytic.re_digamma_le_log_norm_add_one hz]

theorem uniform_re_exactSaddleEquation_cone_lower {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η : ℝ} (hη : 0 < η)
    (z : ℝ) (j : ℤ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ t →
      Real.log t - C ≤ (exactSaddleEquation r A z j n (-(t : ℂ) + (y : ℂ) * Complex.I)).re := by
  let D := 1 + 9 / η + 4 * Real.pi
  let C := (∑ i, Real.log (A i + 3)) + (r : ℝ) * D + ((r : ℝ) - 1) + |Real.log z|
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  have hupper : ∀ᶠ n : ℕ in atTop, ∀ i, 4 ≤ A i * n :=
    Filter.eventually_all.mpr (fun i => (eventually_affine_conditions (by omega : 0 < r) (hA i) 0).mono
      (fun _ h => h.1))
  filter_upwards [uniform_scaled_digamma_im_smallParameter hr hη, hupper,
    (largeScale_tendsto (show 1 < r by omega)).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hψ hupper hR hn t ht y hy hyt
  have hRn : largeScale r n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le
    (by exact_mod_cast hn) (by linarith [div_nonneg zero_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : 1 - 1 / (r : ℝ) ≤ 1)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hb : ‖Complex.digamma ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.log ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤ D :=
    (hψ _ (by simpa using hy)).trans (mul_le_of_le_one_right hD (smallParameter_le_one r hn))
  have hleft := Analytic.re_digamma_left_tail_ge hR ht hb
  have hu (i : Fin (r - 1)) := re_digamma_right_cone_le (hA i).le
    (show 0 ≤ largeScale r n by linarith) hRn hn ht hyt (hupper i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hlog := log_largeScale (by omega : 0 < r) (by omega : 0 < n)
  have hC := le_max_right 0 C
  simp only [exactSaddleEquation, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.re_sum, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, sub_zero, add_zero]
  dsimp only [C] at hC ⊢
  nlinarith [le_abs_self (Real.log z)]

end ThisWork
