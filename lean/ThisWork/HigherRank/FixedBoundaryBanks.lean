module

public import ThisWork.HigherRank.ReflectedVerticalBounds
public import ThisWork.HigherRank.BoundaryReflectionBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! On the fixed Hankel banks of height one, the reflection errors are a
small fraction of the positive real kernel far to the left. -/

@[expose] public section
namespace ThisWork.HigherRank

theorem exp_one_sub_two_pi_le : Real.exp (1 - 2 * Real.pi) ≤ 1 / 16 := by
  have he : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    _ = 1 / Real.exp 4 := by rw [Real.exp_neg, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by norm_num) he

theorem sin_pi_ne_zero_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.mpr
  intro k he
  have hi : Real.pi * w.im = 0 := by simpa [Complex.mul_im] using congrArg Complex.im he
  exact hw ((mul_eq_zero.mp hi).resolve_left Real.pi_ne_zero)

theorem fixed_boundary_bank_errors_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ≤ -(6 * (r : ℝ))) :
    ‖boundaryKernel r m A z n ((x : ℂ) + Complex.I)‖ ≤
      (Real.pi / 4) * ‖reflectedKernel r m A z n (x : ℂ)‖ ∧
    ‖boundaryKernel r m A z n ((x : ℂ) - Complex.I) -
      2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r m A z n ((x : ℂ) - Complex.I)‖ ≤
      (Real.pi / 4) * ‖reflectedKernel r m A z n (x : ℂ)‖ := by
  have he : Real.exp (-2 * Real.pi) ≤ 1 / 2 := by
    have h := (Real.exp_le_exp.mpr (show -2 * Real.pi ≤ 1 - 2 * Real.pi by linarith)).trans exp_one_sub_two_pi_le
    linarith
  have hp := norm_boundaryKernel_upper_le hr m A z n
    (sin_pi_ne_zero_of_im_ne_zero (w := (x : ℂ) + Complex.I) (by simp))
    (by simpa using he)
  have hm := norm_boundaryKernel_lower_error_le hr m A z n
    (sin_pi_ne_zero_of_im_ne_zero (w := (x : ℂ) - Complex.I) (by simp))
    (by simpa using he)
  have hqp := norm_reflectedKernel_fixed_bank_le hr hA m z n hx (h := 1) (by norm_num)
  have hqm := norm_reflectedKernel_fixed_bank_le hr hA m z n hx (h := -1) (by norm_num)
  simp only [Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul, ← sub_eq_add_neg,
    Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_add, zero_sub,
    mul_one, mul_neg] at hp hm hqp hqm
  simp only [← neg_mul] at hp hm
  have habsorb {X Y : ℝ} (hX : X ≤ 4 * Real.pi * Real.exp (-2 * Real.pi) * Y)
      (hY : Y ≤ ‖reflectedKernel r m A z n (x : ℂ)‖ * Real.exp 1) :
      X ≤ (Real.pi / 4) * ‖reflectedKernel r m A z n (x : ℂ)‖ := by
    have hcoef : 4 * Real.pi * Real.exp (1 - 2 * Real.pi) ≤ Real.pi / 4 := by
      nlinarith [mul_le_mul_of_nonneg_left exp_one_sub_two_pi_le (show 0 ≤ 4 * Real.pi by positivity)]
    have hexp : Real.exp (-2 * Real.pi) * Real.exp 1 = Real.exp (1 - 2 * Real.pi) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ 4 * Real.pi * Real.exp (-2 * Real.pi) *
          (‖reflectedKernel r m A z n (x : ℂ)‖ * Real.exp 1) :=
        hX.trans (mul_le_mul_of_nonneg_left hY (by positivity))
      _ = (4 * Real.pi * Real.exp (1 - 2 * Real.pi)) * ‖reflectedKernel r m A z n (x : ℂ)‖ := by
        rw [show 4 * Real.pi * Real.exp (-2 * Real.pi) *
            (‖reflectedKernel r m A z n (x : ℂ)‖ * Real.exp 1) =
            (4 * Real.pi * (Real.exp (-2 * Real.pi) * Real.exp 1)) * ‖reflectedKernel r m A z n (x : ℂ)‖ by ring, hexp]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  exact ⟨habsorb hp hqp, habsorb hm hqm⟩

theorem norm_reflectedKernel_lower_le_boundary {r : ℕ} (hr : 0 < r)
    (m : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) (x : ℝ) :
    Real.pi * ‖reflectedKernel r m A z n ((x : ℂ) - Complex.I)‖ ≤
      ‖boundaryKernel r m A z n ((x : ℂ) - Complex.I)‖ := by
  have he : Real.exp (-2 * Real.pi) ≤ 1 / 16 :=
    (Real.exp_le_exp.mpr (by linarith : -2 * Real.pi ≤ 1 - 2 * Real.pi)).trans exp_one_sub_two_pi_le
  have h := norm_boundaryKernel_lower_error_le hr m A z n
    (sin_pi_ne_zero_of_im_ne_zero (w := (x : ℂ) - Complex.I) (by simp))
    (by
      have he' : Real.exp (-2 * Real.pi) ≤ 1 / 2 := by linarith
      simpa [neg_mul] using he')
  have ht := norm_sub_le (boundaryKernel r m A z n ((x : ℂ) - Complex.I))
    (boundaryKernel r m A z n ((x : ℂ) - Complex.I) -
      2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r m A z n ((x : ℂ) - Complex.I))
  rw [sub_sub_cancel] at ht
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_ofNat, Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub, mul_neg,
    mul_one, ← neg_mul] at ht h
  have hc := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 4 * Real.pi * ‖reflectedKernel r m A z n ((x : ℂ) - Complex.I)‖ by positivity)
  nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg (reflectedKernel r m A z n ((x : ℂ) - Complex.I)))]

theorem norm_reflectedKernel_real_le_boundary {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ≤ -(6 * (r : ℝ))) :
    ‖reflectedKernel r m A z n (x : ℂ)‖ ≤
      (Real.exp 1 / Real.pi) * ‖boundaryKernel r m A z n ((x : ℂ) - Complex.I)‖ := by
  have hreal := norm_reflectedKernel_real_le_fixed_bank hr hA m z n hx (h := -1) (by norm_num)
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] at hreal
  have hbound := norm_reflectedKernel_lower_le_boundary hr m A z n x
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hreal Real.pi_pos.le,
    mul_le_mul_of_nonneg_left hbound (Real.exp_pos 1).le]

end ThisWork.HigherRank
