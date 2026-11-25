module

public import ThisWork.ReflectedGammaNorm

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology

theorem norm_real_scale_le {R M : ℝ} (hR : 0 ≤ R) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖(R : ℂ) * s‖ ≤ R * M := by
  rw [norm_mul, Complex.norm_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left hs hR

theorem uniform_scaled_gammaNormError_right {κ M : ℝ} (hκ : 0 < κ) (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re →
      |gammaNormError ((R : ℂ) * s)| ≤ C * (1 + Real.log R) := by
  let B := |gammaNormError 2| + 2 * |Real.log M| + 2 * M / κ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B + 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 / κ)] with R hR₁ hRκ
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR₁
  refine ⟨hR, fun s hs hκs => ?_⟩
  have hden : R * κ ≤ ((R : ℂ) * s).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left hκs hR.le
  have h2 : 2 ≤ ((R : ℂ) * s).re := ((div_le_iff₀ hκ).mp hRκ).trans hden
  have hnorm := norm_real_scale_le hR.le hs
  have hlog : Real.log (((R : ℂ) * s).re) ≤ Real.log R + Real.log M := by
    have h := Real.log_le_log (show 0 < ((R : ℂ) * s).re by linarith)
      ((Complex.re_le_norm _).trans hnorm)
    simpa only [Real.log_mul hR.ne' hM.ne'] using h
  have him : |((R : ℂ) * s).im| ≤ R * M := (Complex.abs_im_le_norm _).trans hnorm
  have hratio : 2 * |((R : ℂ) * s).im| / ((R : ℂ) * s).re ≤ 2 * M / κ := by
    apply (div_le_div_iff₀ (by linarith : 0 < ((R : ℂ) * s).re) hκ).mpr
    nlinarith [mul_le_mul_of_nonneg_right him hκ.le, mul_le_mul_of_nonneg_left hden hM.le]
  have herror : |gammaNormError ((R : ℂ) * s)| ≤ B + 2 * Real.log R := by
    dsimp only [B]
    linarith [abs_gammaNormError_right h2, le_abs_self (Real.log M)]
  exact herror.trans (by nlinarith [Real.log_nonneg hR₁])

end ThisWork.Analytic
