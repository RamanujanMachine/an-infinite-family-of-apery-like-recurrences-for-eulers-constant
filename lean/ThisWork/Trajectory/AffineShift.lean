module

public import ThisWork.Trajectory.SqrtParameters
public import ThisWork.AffineDigamma

/-! The additional moving left Gamma factor in the double-minimum kernel. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

/-- Uniform digamma control for the new factor `Gamma(A+R*s)`. -/
theorem norm_digamma_affine_add_sub_log_le {A R M : ℝ}
    (hA : 4 ≤ A) (hR : 0 ≤ R) (hRM : R * M ≤ A / 4)
    {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖Complex.digamma ((A : ℂ) + (R : ℂ) * s) - Complex.log (A : ℂ)‖ ≤
      (4 / A + (3 / 2 : ℝ) * ((1 + R * M) / A)) + 2 / A := by
  have hshift := Analytic.norm_digamma_affine_sub_log_le hA hR hRM
    (s := -s) (by simpa only [norm_neg] using hs)
  have hre : A / 2 ≤ ((A : ℂ) + (R : ℂ) * s).re := by
    have h := mul_le_mul_of_nonneg_left (neg_le_of_abs_le
      ((Complex.abs_re_le_norm s).trans hs)) hR
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hinv : ‖1 / ((A : ℂ) + (R : ℂ) * s)‖ ≤ 2 / A := by
    rw [norm_div, norm_one]
    calc
      _ ≤ 1 / (A / 2) := div_le_div_of_nonneg_left zero_le_one
        (by linarith) (hre.trans (Complex.re_le_norm _))
      _ = _ := by ring
  have hψ := Complex.digamma_apply_add_one ((A : ℂ) + (R : ℂ) * s)
    (Analytic.not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by linarith : 0 < ((A : ℂ) + (R : ℂ) * s).re))))
  calc
    _ = ‖(Complex.digamma ((A : ℂ) + (R : ℂ) * s + 1) - Complex.log (A : ℂ)) -
        1 / ((A : ℂ) + (R : ℂ) * s)‖ := by rw [hψ, one_div]; congr 1; ring
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add
      (by simpa only [mul_neg, sub_neg_eq_add] using hshift) hinv)

end ThisWork.Trajectory
