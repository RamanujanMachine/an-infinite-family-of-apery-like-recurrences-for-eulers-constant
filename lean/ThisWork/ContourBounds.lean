module

public import ThisWork.LimitingPhase
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Phase inequalities for explicit polygonal Hankel contours. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

/-- The real part of the phase on a horizontal line. -/
noncomputable def horizontalPhase (j : Branch) (c height x : ℝ) : ℝ :=
  (limitingPhase j c ((x : ℂ) + (height : ℂ) * Complex.I)).re

theorem hasDerivAt_horizontalPhase (j : Branch) {c height : ℝ} (hc : 0 < c)
    (hh : height ≠ 0) (x : ℝ) :
    HasDerivAt (horizontalPhase j c height)
      (3 * Real.log ‖((x : ℂ) + (height : ℂ) * Complex.I) / (c : ℂ)‖) x := by
  have hs : (x : ℂ) + (height : ℂ) * Complex.I ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using hh
  have h := (hasDerivAt_limitingPhase j hc ((div_pos_real_mem_slitPlane_iff hc _).mpr hs)).comp
    (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((height : ℂ) * Complex.I))
  change HasDerivAt (fun x : ℝ => (limitingPhase j c ((x : ℂ) + (height : ℂ) * Complex.I)).re) _ x
  simpa only [Function.comp_def, id_eq, mul_one, limitingEquation_re] using h.real_of_complex

theorem norm_horizontal_div_sq {c : ℝ} (hc : 0 < c) (x height : ℝ) :
    ‖((x : ℂ) + (height : ℂ) * Complex.I) / (c : ℂ)‖ ^ 2 = (x ^ 2 + height ^ 2) / c ^ 2 := by
  rw [norm_div, Complex.norm_of_nonneg hc.le, div_pow, Complex.sq_norm, Complex.normSq_add_mul_I]

theorem norm_horizontal_div_lt_one {c : ℝ} (hc : 0 < c) (x height : ℝ) :
    ‖((x : ℂ) + (height : ℂ) * Complex.I) / (c : ℂ)‖ < 1 ↔ x ^ 2 + height ^ 2 < c ^ 2 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, norm_horizontal_div_sq hc,
    one_pow, div_lt_iff₀ (sq_pos_of_pos hc), one_mul]

theorem one_lt_norm_horizontal_div {c : ℝ} (hc : 0 < c) (x height : ℝ) :
    1 < ‖((x : ℂ) + (height : ℂ) * Complex.I) / (c : ℂ)‖ ↔ c ^ 2 < x ^ 2 + height ^ 2 := by
  rw [← sq_lt_sq₀ zero_le_one (norm_nonneg _), norm_horizontal_div_sq hc,
    one_pow, lt_div_iff₀ (sq_pos_of_pos hc), one_mul]

theorem norm_horizontal_div_pos {c height : ℝ} (hc : 0 < c) (hh : height ≠ 0) (x : ℝ) :
    0 < ‖((x : ℂ) + (height : ℂ) * Complex.I) / (c : ℂ)‖ := by
  apply norm_pos_iff.mpr
  apply div_ne_zero ?_ (Complex.ofReal_ne_zero.mpr hc.ne')
  intro h
  apply hh
  simpa using congrArg Complex.im h

/-- On each horizontal tail, the limiting real phase increases strictly toward
the saddle. This is a global inequality, not just a local quadratic estimate. -/
theorem horizontalPhase_strictMono_left (j : Branch) {c height R : ℝ}
    (hc : 0 < c) (hh : height ≠ 0) (hR : 0 < R) (hcircle : R ^ 2 + height ^ 2 = c ^ 2) :
    StrictMonoOn (horizontalPhase j c height) (Iic (-R)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic (-R))
  · exact (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_horizontalPhase j hc hh x).continuousAt)).continuousOn
  · intro x hx
    rw [(hasDerivAt_horizontalPhase j hc hh x).deriv]
    apply mul_pos (by norm_num)
    apply Real.log_pos
    apply (one_lt_norm_horizontal_div hc x height).mpr
    have hxR : x < -R := by simpa only [interior_Iic, mem_Iio] using hx
    have hs : R ^ 2 < (-x) ^ 2 :=
      (sq_lt_sq₀ hR.le (by linarith)).mpr (by linarith)
    nlinarith

/-- Between the two intersections with the circle `|s| = c`, the horizontal
real phase decreases strictly. -/
theorem horizontalPhase_strictAnti_middle (j : Branch) {c height R : ℝ}
    (hc : 0 < c) (hh : height ≠ 0) (_hR : 0 < R) (hcircle : R ^ 2 + height ^ 2 = c ^ 2) :
    StrictAntiOn (horizontalPhase j c height) (Icc (-R) R) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (-R) R)
  · exact (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_horizontalPhase j hc hh x).continuousAt)).continuousOn
  · intro x hx
    rw [(hasDerivAt_horizontalPhase j hc hh x).deriv]
    apply mul_neg_of_pos_of_neg (by norm_num)
    apply Real.log_neg (norm_horizontal_div_pos hc hh x)
    apply (norm_horizontal_div_lt_one hc x height).mpr
    have hxR : -R < x ∧ x < R := by simpa only [interior_Icc, mem_Ioo] using hx
    nlinarith [mul_pos (sub_pos.mpr hxR.2) (show 0 < x + R by linarith)]

theorem horizontalPhase_strict_max (j : Branch) {c height R x : ℝ}
    (hc : 0 < c) (hh : height ≠ 0) (hR : 0 < R) (hcircle : R ^ 2 + height ^ 2 = c ^ 2)
    (hx : x ≤ R) (hne : x ≠ -R) :
    horizontalPhase j c height x < horizontalPhase j c height (-R) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact horizontalPhase_strictMono_left j hc hh hR hcircle h.le le_rfl h
  · exact horizontalPhase_strictAnti_middle j hc hh hR hcircle
      ⟨le_rfl, by linarith⟩ ⟨h.le, hx⟩ h

/-- The real part of the phase on the right vertical edge of a Hankel contour. -/
noncomputable def verticalPhase (j : Branch) (c right y : ℝ) : ℝ :=
  (limitingPhase j c ((right : ℂ) + (y : ℂ) * Complex.I)).re

theorem hasDerivAt_verticalPhase (j : Branch) {c right : ℝ} (hc : 0 < c)
    (hr : 0 < right) (y : ℝ) :
    HasDerivAt (verticalPhase j c right)
      (-3 * Complex.arg (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)) - (twist j).im) y := by
  have hs : (right : ℂ) + (y : ℂ) * Complex.I ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using hr
  have h := (hasDerivAt_limitingPhase j hc ((div_pos_real_mem_slitPlane_iff hc _).mpr hs)).comp
    (y : ℂ) (((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (right : ℂ))
  change HasDerivAt (fun y : ℝ => (limitingPhase j c ((right : ℂ) + (y : ℂ) * Complex.I)).re) _ y
  simpa [Function.comp_def, limitingEquation, Complex.mul_re, Complex.mul_im, Complex.log_im, sub_eq_add_neg, add_comm] using h.real_of_complex

theorem arg_vertical_div_bounds {c right : ℝ} (hc : 0 < c) (hr : 0 < right) (y : ℝ) :
    -(Real.pi / 2) < Complex.arg (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)) ∧
      Complex.arg (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)) < Real.pi / 2 := by
  apply abs_lt.mp
  apply Complex.abs_arg_lt_pi_div_two_iff.mpr
  left
  rw [Complex.div_ofReal_re]
  simpa using div_pos hr hc

theorem verticalPhase_strictAnti_of_twist (j : Branch) {c right : ℝ} (hc : 0 < c)
    (hr : 0 < right) (htwist : 3 * Real.pi / 2 < (twist j).im) :
    StrictAnti (verticalPhase j c right) := by
  apply strictAnti_of_deriv_neg
  intro y
  rw [(hasDerivAt_verticalPhase j hc hr y).deriv]
  have harg := (arg_vertical_div_bounds hc hr y).1
  linarith

theorem verticalPhase_strictMono_of_twist (j : Branch) {c right : ℝ} (hc : 0 < c)
    (hr : 0 < right) (htwist : (twist j).im < -(3 * Real.pi / 2)) :
    StrictMono (verticalPhase j c right) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(hasDerivAt_verticalPhase j hc hr y).deriv]
  have harg := (arg_vertical_div_bounds hc hr y).2
  linarith

theorem verticalPhase_one_strictAnti {c right : ℝ} (hc : 0 < c) (hr : 0 < right) :
    StrictAnti (verticalPhase .one c right) := by
  apply verticalPhase_strictAnti_of_twist .one hc hr
  rw [twist_one]
  norm_num [Complex.mul_im]
  linarith [Real.pi_pos]

theorem verticalPhase_two_strictMono {c right : ℝ} (hc : 0 < c) (hr : 0 < right) :
    StrictMono (verticalPhase .two c right) := by
  apply verticalPhase_strictMono_of_twist .two hc hr
  rw [twist_two]
  norm_num [Complex.mul_im]
  linarith [Real.pi_pos]

theorem horizontalPhase_le_max (j : Branch) {c height R x : ℝ}
    (hc : 0 < c) (hh : height ≠ 0) (hR : 0 < R) (hcircle : R ^ 2 + height ^ 2 = c ^ 2)
    (hx : x ≤ R) : horizontalPhase j c height x ≤ horizontalPhase j c height (-R) := by
  by_cases he : x = -R
  · exact he ▸ le_rfl
  · exact (horizontalPhase_strict_max j hc hh hR hcircle hx he).le

theorem verticalPhase_three_strictMono_lower {c right : ℝ} (hc : 0 < c) (hr : 0 < right) :
    StrictMonoOn (verticalPhase .three c right) (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0)
  · exact (continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_verticalPhase .three hc hr y).continuousAt)).continuousOn
  · intro y hy
    have hy0 : y < 0 := by simpa only [interior_Iic, mem_Iio] using hy
    have him : (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)).im < 0 := by
      rw [Complex.div_ofReal_im]
      simpa using div_neg_of_neg_of_pos hy0 hc
    have harg := Complex.arg_neg_iff.mpr him
    rw [(hasDerivAt_verticalPhase .three hc hr y).deriv, twist_three, Complex.zero_im]
    linarith

theorem verticalPhase_three_strictAnti_upper {c right : ℝ} (hc : 0 < c) (hr : 0 < right) :
    StrictAntiOn (verticalPhase .three c right) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_verticalPhase .three hc hr y).continuousAt)).continuousOn
  · intro y hy
    have hy0 : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
    have him : 0 < (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)).im := by
      rw [Complex.div_ofReal_im]
      simpa using div_pos hy0 hc
    have harg0 := Complex.arg_nonneg_iff.mpr him.le
    have hargne : Complex.arg (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)) ≠ 0 := by
      intro he
      exact him.ne' (Complex.arg_eq_zero_iff.mp he).2
    rw [(hasDerivAt_verticalPhase .three hc hr y).deriv, twist_three, Complex.zero_im]
    have harg : 0 < Complex.arg (((right : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)) :=
      lt_of_le_of_ne harg0 hargne.symm
    linarith

theorem verticalPhase_three_strict_max {c right y : ℝ} (hc : 0 < c) (hr : 0 < right) (hy : y ≠ 0) :
    verticalPhase .three c right y < verticalPhase .three c right 0 := by
  rcases lt_or_gt_of_ne hy with h | h
  · exact verticalPhase_three_strictMono_lower hc hr h.le le_rfl h
  · exact verticalPhase_three_strictAnti_upper hc hr le_rfl h.le h

theorem horizontalPhase_monotone_large_height (j : Branch) {c height : ℝ}
    (hc : 0 < c) (hh : height ≠ 0) (hheight : c ^ 2 ≤ height ^ 2) :
    Monotone (horizontalPhase j c height) := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_horizontalPhase j hc hh x).differentiableAt)
  intro x
  rw [(hasDerivAt_horizontalPhase j hc hh x).deriv]
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  apply (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp
  rw [norm_horizontal_div_sq hc, one_pow, le_div_iff₀ (sq_pos_of_pos hc), one_mul]
  nlinarith [sq_nonneg x]

end ThisWork
