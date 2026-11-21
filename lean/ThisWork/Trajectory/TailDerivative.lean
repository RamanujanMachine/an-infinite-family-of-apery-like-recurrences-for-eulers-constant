module

public import ThisWork.Trajectory.TailGeometry
public import ThisWork.Trajectory.KernelSaddle
public import ThisWork.ImaginaryDigamma

/-! Uniform left-tail bounds for the actual square-root-scaled saddle equation. -/

public section

namespace ThisWork.Trajectory

open Set Filter
open scoped Topology

private theorem log_norm_right_factor_tail_le {A R t y H : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hR : 1 ≤ R) (hsq : R ^ 2 = (n : ℝ)) (ht : 1 ≤ t) (hy : |y| ≤ H) :
    Real.log ‖(A : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ ≤
      Real.log (A + H + 2) + Real.log R + Real.log (R + t) := by
  have hH : 0 ≤ H := (abs_nonneg y).trans hy
  have hpos : 0 < ‖(A : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ := by
    apply lt_of_lt_of_le (b := (_ : ℂ).re) ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, Complex.neg_re,
      Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
    nlinarith [mul_nonneg hA (Nat.cast_nonneg (α := ℝ) n),
      mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ t by linarith)]
  have h := Real.log_le_log hpos (norm_right_factor_sqrt_tail_le hA hR hsq ht hy)
  simpa only [Real.log_mul (show (A + H + 2) * R ≠ 0 by positivity)
    (show R + t ≠ 0 by linarith), Real.log_mul
    (show A + H + 2 ≠ 0 by positivity) (show R ≠ 0 by linarith)] using h

/-- A uniform logarithmic product bound across all three left-tail regions. -/
theorem log_tail_gamma_ratio_lower {d : ℕ} {A₁ A₂ R t y η H : ℝ} {n : ℕ}
    (hd : 0 < d) (h₁ : 0 ≤ A₁) (h₂ : 0 ≤ A₂) (hR : 1 ≤ R)
    (hsq : R ^ 2 = (n : ℝ)) (ht : 1 ≤ t) (hη : 0 < η) (hy : η ≤ |y|) (hyH : |y| ≤ H) :
    Real.log t - (Real.log (tailGeometryConstant d η) +
      Real.log (A₁ + H + 2) + Real.log (A₂ + H + 2)) ≤
      2 * Real.log ‖(R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ +
      Real.log ‖(d : ℂ) * n + (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)‖ -
      Real.log ‖(A₁ : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ -
      Real.log ‖(A₂ : ℂ) * n - (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1‖ := by
  let x : ℂ := (R : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)
  let q : ℂ := (((d : ℝ) * R - t : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  have hqη : η ≤ ‖q‖ := hy.trans (by simpa [q] using Complex.abs_im_le_norm q)
  have hq0 : 0 < ‖q‖ := hη.trans_le hqη
  have hq : |(d : ℝ) * R - t| ≤ ‖q‖ := by simpa [q] using Complex.abs_re_le_norm q
  have hgeo := tail_geometry (by exact_mod_cast hd : (1 : ℝ) ≤ d) hR ht hη hqη hq
  have hC : 0 < tailGeometryConstant (d : ℝ) η :=
    (show (0 : ℝ) < 8 by norm_num).trans_le
      ((le_max_right _ _).trans (le_max_right _ _))
  have hsmall : R * t ≤ ‖x‖ := by
    have h := Complex.abs_re_le_norm x
    simpa [x, Complex.mul_re, abs_mul, abs_of_nonneg hR0.le, abs_of_nonneg ht0.le] using h
  have hlogsmall : Real.log R + Real.log t ≤ Real.log ‖x‖ := by
    simpa only [Real.log_mul hR0.ne' ht0.ne'] using Real.log_le_log (mul_pos hR0 ht0) hsmall
  have hshift : (d : ℂ) * n + x = (R : ℂ) * q := by
    have hnC : (n : ℂ) = (R : ℂ) ^ 2 := by exact_mod_cast hsq.symm
    dsimp only [x, q]
    rw [hnC]
    push_cast
    ring
  have hlogshift : Real.log ‖(d : ℂ) * n + x‖ = Real.log R + Real.log ‖q‖ := by
    rw [hshift, norm_mul, Complex.norm_of_nonneg hR0.le, Real.log_mul hR0.ne' hq0.ne']
  have hloggeo := Real.log_le_log (sq_pos_of_pos (add_pos hR0 ht0)) hgeo
  rw [Real.log_pow,
    Real.log_mul (mul_pos (mul_pos hC hR0) ht0).ne' hq0.ne',
    Real.log_mul (mul_pos hC hR0).ne' ht0.ne', Real.log_mul hC.ne' hR0.ne'] at hloggeo
  change Real.log t - _ ≤ 2 * Real.log ‖x‖ + Real.log ‖(d : ℂ) * n + x‖ -
    Real.log ‖(A₁ : ℂ) * n - x + 1‖ - Real.log ‖(A₂ : ℂ) * n - x + 1‖
  rw [hlogshift]
  norm_num only [Nat.cast_ofNat] at hloggeo
  dsimp only [x] at hlogsmall ⊢
  linarith [log_norm_right_factor_tail_le h₁ hR hsq ht hyH,
    log_norm_right_factor_tail_le h₂ hR hsq ht hyH]

private theorem log_norm_sub_one_le_re_digamma {w : ℂ}
    (hb : ‖Complex.digamma w - Complex.log w‖ ≤ 1) :
    Real.log ‖w‖ - 1 ≤ (Complex.digamma w).re := by
  have h : Real.log ‖w‖ - (Complex.digamma w).re ≤ 1 := by
    simpa only [Complex.sub_re, Complex.log_re, norm_sub_rev] using
      (Complex.re_le_norm (Complex.log w - Complex.digamma w)).trans
        (by simpa only [norm_sub_rev] using hb)
  linarith

/-- A global left-tail lower bound for the actual equation, including `x ≈ -dn`. -/
theorem uniform_re_exactSqrtEquation_left_lower {d : ℕ} {A₁ A₂ z η H : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂)
    (hη : 0 < η) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log t - C ≤
        (exactSqrtEquation d A₁ A₂ z j n (-(t : ℂ) + (y : ℂ) * Complex.I)).re := by
  let C := Real.log (tailGeometryConstant d η) + Real.log (A₁ + H + 2) +
    Real.log (A₂ + H + 2) + 5 + |Real.log z|
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  filter_upwards [sqrtScale_tendsto.eventually (Analytic.uniform_scaled_digamma_im hη zero_lt_one),
    eventually_right_factor_conditions h₁ 0, eventually_right_factor_conditions h₂ 0,
    sqrtScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with n hψ hA₁ hA₂ hR hn t ht y hy hyH
  have hψ₀ := hψ.2 (-(t : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)
  have hψD := hψ.2 ((((d : ℝ) * sqrtScale n - t : ℝ) : ℂ) + (y : ℂ) * Complex.I)
    (by simpa using hy)
  have hshift : (sqrtScale n : ℂ) *
      ((((d : ℝ) * sqrtScale n - t : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
      (d : ℂ) * n + (sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) := by
    have hnC : (n : ℂ) = (sqrtScale n : ℂ) ^ 2 := by exact_mod_cast (sqrtScale_sq n).symm
    rw [hnC]
    push_cast
    ring
  rw [hshift] at hψD
  have hright (A : ℝ) (hA : 4 ≤ A * n) :
      2 ≤ ((A : ℂ) * n - (sqrtScale n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I) + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, Complex.neg_re,
      Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
    nlinarith [mul_nonneg hψ.1.le (show 0 ≤ t by linarith)]
  have hgeo := log_tail_gamma_ratio_lower hd h₁.le h₂.le hR (sqrtScale_sq n) ht hη hy hyH
  have hlow₀ := log_norm_sub_one_le_re_digamma hψ₀
  have hlowD := log_norm_sub_one_le_re_digamma hψD
  have hu₁ := Analytic.re_digamma_le_log_norm_add_one (hright A₁ hA₁.1)
  have hu₂ := Analytic.re_digamma_le_log_norm_add_one (hright A₂ hA₂.1)
  have hmax := le_max_right (0 : ℝ) C
  simp only [exactSqrtEquation, kernelLogDerivative, Complex.ofReal_re, Complex.add_re,
    Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
    twist_re, add_zero]
  dsimp only [C] at hmax ⊢
  linarith [le_abs_self (Real.log z)]

end ThisWork.Trajectory
