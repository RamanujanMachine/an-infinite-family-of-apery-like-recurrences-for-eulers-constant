module

public import ThisWork.Argument
public import ThisWork.ScaledDigamma
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Uniform control of the two right-hand Gamma factors after normalization. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem norm_digamma_affine_sub_log_le {A R M : ℝ} (hA : 4 ≤ A) (hR : 0 ≤ R)
    (hRM : R * M ≤ A / 4) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖Complex.digamma ((A : ℂ) - (R : ℂ) * s + 1) - Complex.log (A : ℂ)‖ ≤
      4 / A + (3 / 2 : ℝ) * ((1 + R * M) / A) := by
  have hA0 : 0 < A := by linarith
  have hAC0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA0.ne'
  let u : ℂ := (A : ℂ) - (R : ℂ) * s + 1
  let q : ℂ := (1 - (R : ℂ) * s) / (A : ℂ)
  have hRe : A / 2 ≤ u.re := by
    have hsr : s.re ≤ M := (Complex.re_le_norm s).trans hs
    have hm := mul_le_mul_of_nonneg_left hsr hR
    dsimp [u]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hpsi : ‖Complex.digamma u - Complex.log u‖ ≤ 4 / A := by
    have h := norm_digamma_sub_log_le_two_div (s := u) (by linarith)
    exact (h.trans (div_le_div_of_nonneg_left (by norm_num) (half_pos hA0) hRe)).trans_eq (by field_simp; norm_num)
  have hqnorm : ‖q‖ ≤ (1 + R * M) / A := by
    rw [show q = (1 - (R : ℂ) * s) / (A : ℂ) from rfl, norm_div, Complex.norm_of_nonneg hA0.le]
    apply div_le_div_of_nonneg_right ?_ hA0.le
    have h := norm_sub_le (1 : ℂ) ((R : ℂ) * s)
    simp only [norm_one, norm_mul, Complex.norm_of_nonneg hR] at h
    exact h.trans (add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hs hR))
  have hqhalf : ‖q‖ ≤ 1 / 2 := hqnorm.trans ((div_le_iff₀ hA0).mpr (by nlinarith))
  have hlog : ‖Complex.log (1 + q)‖ ≤ (3 / 2 : ℝ) * ((1 + R * M) / A) :=
    (Complex.norm_log_one_add_half_le_self hqhalf).trans
      (mul_le_mul_of_nonneg_left hqnorm (by norm_num))
  have hqne : 1 + q ≠ 0 := by
    intro he
    have hqeq : q = -1 := by linear_combination he
    have hbad : (1 : ℝ) ≤ 1 / 2 := by simpa only [hqeq, norm_neg, norm_one] using hqhalf
    norm_num at hbad
  have hprod : u = (A : ℂ) * (1 + q) := by
    dsimp [u, q]
    field_simp [hAC0]
    ring
  have hlogEq : Complex.log u - Complex.log (A : ℂ) = Complex.log (1 + q) := by
    rw [hprod, Complex.log_ofReal_mul hA0 hqne, ← Complex.ofReal_log hA0.le]
    ring
  have htri := norm_add_le (Complex.digamma u - Complex.log u) (Complex.log u - Complex.log (A : ℂ))
  have hbound := htri.trans (add_le_add hpsi (hlogEq ▸ hlog))
  simpa only [sub_add_sub_cancel] using hbound

end ThisWork.Analytic
