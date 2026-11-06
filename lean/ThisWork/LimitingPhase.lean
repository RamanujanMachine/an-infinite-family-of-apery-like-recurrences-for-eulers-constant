module

public import Neuschel.UniformLocal
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The limiting logarithmic phase in Appendix A of this work -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

/-- The labels correspond to `j = 1, 2, 3` in Lemma 8. -/
inductive Branch where
  | one | two | three
  deriving DecidableEq

noncomputable def saddleAngle : Branch → ℝ
  | .one => -(2 * Real.pi / 3)
  | .two => 2 * Real.pi / 3
  | .three => 0

noncomputable def twist (j : Branch) : ℂ := -3 * ((saddleAngle j : ℂ) * Complex.I)

noncomputable def rho (j : Branch) : ℂ := Complex.exp ((saddleAngle j : ℂ) * Complex.I)

noncomputable def limitingEquation (j : Branch) (c : ℝ) (s : ℂ) : ℂ :=
  3 * Complex.log (s / (c : ℂ)) + twist j

noncomputable def limitingPhase (j : Branch) (c : ℝ) (s : ℂ) : ℂ :=
  s * (limitingEquation j c s - 3)

theorem saddleAngle_mem (j : Branch) : saddleAngle j ∈ Ioo (-Real.pi) Real.pi := by
  cases j <;> simp only [saddleAngle, mem_Ioo]
  all_goals constructor <;> linarith [Real.pi_pos]

@[simp] theorem rho_ne_zero (j : Branch) : rho j ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem norm_rho (j : Branch) : ‖rho j‖ = 1 := by
  simp [rho, Complex.norm_exp, Complex.mul_re]

theorem log_rho (j : Branch) : Complex.log (rho j) = (saddleAngle j : ℂ) * Complex.I := by
  apply Complex.log_exp
  · simpa using (saddleAngle_mem j).1
  · simpa using (saddleAngle_mem j).2.le

theorem arg_rho (j : Branch) : Complex.arg (rho j) = saddleAngle j := by
  rw [← Complex.log_im, log_rho]
  simp

theorem rho_mem_slitPlane (j : Branch) : rho j ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff_arg.mpr ⟨by rw [arg_rho]; exact (saddleAngle_mem j).2.ne,
    rho_ne_zero j⟩

theorem limitingEquation_saddle (j : Branch) {c : ℝ} (hc : 0 < c) :
    limitingEquation j c ((c : ℂ) * rho j) = 0 := by
  rw [limitingEquation, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hc.ne'), log_rho, twist]
  ring

theorem limitingPhase_saddle (j : Branch) {c : ℝ} (hc : 0 < c) :
    limitingPhase j c ((c : ℂ) * rho j) = -3 * (c : ℂ) * rho j := by
  rw [limitingPhase, limitingEquation_saddle j hc]
  ring

theorem hasDerivAt_log_scale {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℂ => Complex.log (t / (c : ℂ))) (1 / s) s := by
  have h := ((hasDerivAt_id s).div_const (c : ℂ)).clog hs
  exact h.congr_deriv (by simp only [id_eq]; field_simp [Complex.ofReal_ne_zero.mpr hc.ne'])

theorem hasDerivAt_limitingEquation (j : Branch) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (limitingEquation j c) (3 / s) s := by
  convert ((hasDerivAt_log_scale hc hs).const_mul 3).add_const (twist j) using 1
  · rfl
  · simp only [mul_one_div]

theorem hasDerivAt_limitingPhase (j : Branch) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (limitingPhase j c) (limitingEquation j c s) s := by
  have h := (hasDerivAt_id s).mul ((hasDerivAt_limitingEquation j hc hs).sub_const 3)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  convert h using 1
  · rfl
  · simp only [one_mul, id_eq, mul_div_cancel₀ _ hs0, sub_add_cancel]

theorem div_pos_real_mem_slitPlane_iff {c : ℝ} (hc : 0 < c) (s : ℂ) :
    s / (c : ℂ) ∈ Complex.slitPlane ↔ s ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, Complex.div_ofReal_re, Complex.div_ofReal_im,
    div_pos_iff_of_pos_right hc, ne_eq, div_eq_zero_iff, hc.ne', or_false]

theorem differentiableOn_limitingPhase (j : Branch) {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (limitingPhase j c) Complex.slitPlane :=
  fun s hs => (hasDerivAt_limitingPhase j hc ((div_pos_real_mem_slitPlane_iff hc s).mpr hs)).differentiableAt.differentiableWithinAt

theorem deriv_limitingPhase (j : Branch) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ Complex.slitPlane) : deriv (limitingPhase j c) s = limitingEquation j c s :=
  (hasDerivAt_limitingPhase j hc ((div_pos_real_mem_slitPlane_iff hc s).mpr hs)).deriv

theorem hasDerivAt_limitingEquation_saddle (j : Branch) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (limitingEquation j c) (3 / ((c : ℂ) * rho j)) ((c : ℂ) * rho j) :=
  hasDerivAt_limitingEquation j hc (by
    rw [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hc.ne')]
    exact rho_mem_slitPlane j)

theorem limitingEquation_saddle_simple (j : Branch) {c : ℝ} (hc : 0 < c) :
    deriv (limitingEquation j c) ((c : ℂ) * rho j) ≠ 0 := by
  rw [(hasDerivAt_limitingEquation_saddle j hc).deriv]
  exact div_ne_zero (by norm_num) (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') (rho_ne_zero j))

theorem limitingEquation_eq_zero_iff (j : Branch) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ Complex.slitPlane) : limitingEquation j c s = 0 ↔ s = (c : ℂ) * rho j := by
  constructor
  · intro hz
    have he : Complex.log (s / (c : ℂ)) = (saddleAngle j : ℂ) * Complex.I := by
      dsimp [limitingEquation, twist] at hz
      linear_combination hz / 3
    have hr : s / (c : ℂ) = rho j := by
      rw [← Complex.exp_log (Complex.slitPlane_ne_zero ((div_pos_real_mem_slitPlane_iff hc s).mpr hs)), he]
      rfl
    exact ((div_eq_iff (Complex.ofReal_ne_zero.mpr hc.ne')).mp hr).trans (mul_comm _ _)
  · rintro rfl
    exact limitingEquation_saddle j hc

theorem limitingPhase_unique_saddle (j : Branch) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ Complex.slitPlane) : deriv (limitingPhase j c) s = 0 ↔ s = (c : ℂ) * rho j := by
  rw [deriv_limitingPhase j hc hs]
  exact limitingEquation_eq_zero_iff j hc hs

theorem twist_one : twist .one = 2 * (Real.pi : ℂ) * Complex.I := by
  simp only [twist, saddleAngle, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem twist_two : twist .two = -2 * (Real.pi : ℂ) * Complex.I := by
  simp only [twist, saddleAngle, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

@[simp] theorem twist_three : twist .three = 0 := by simp [twist, saddleAngle]

@[simp] theorem rho_three : rho .three = 1 := by simp [rho, saddleAngle]

theorem rho_one_re : (rho .one).re = -1 / 2 := by
  have he : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  norm_num [rho, saddleAngle, Complex.exp_re, he, Real.cos_pi_div_three]

theorem rho_two_re : (rho .two).re = -1 / 2 := by
  have he : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  norm_num [rho, saddleAngle, Complex.exp_re, he, Real.cos_pi_div_three]

theorem rho_one_im : (rho .one).im = -(Real.sqrt 3 / 2) := by
  have he : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  norm_num [rho, saddleAngle, Complex.exp_im, he, Real.sin_pi_div_three]

theorem rho_two_im : (rho .two).im = Real.sqrt 3 / 2 := by
  have he : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  norm_num [rho, saddleAngle, Complex.exp_im, he, Real.sin_pi_div_three]

theorem limitingPhase_one_saddle_re {c : ℝ} (hc : 0 < c) :
    (limitingPhase .one c ((c : ℂ) * rho .one)).re = 3 * c / 2 := by
  rw [limitingPhase_saddle .one hc]
  simp [Complex.mul_re, rho_one_re]
  ring

theorem limitingPhase_two_saddle_re {c : ℝ} (hc : 0 < c) :
    (limitingPhase .two c ((c : ℂ) * rho .two)).re = 3 * c / 2 := by
  rw [limitingPhase_saddle .two hc]
  simp [Complex.mul_re, rho_two_re]
  ring

theorem limitingPhase_three_saddle_re {c : ℝ} (hc : 0 < c) :
    (limitingPhase .three c ((c : ℂ) * rho .three)).re = -3 * c := by
  rw [limitingPhase_saddle .three hc, rho_three]
  simp

@[simp] theorem twist_re (j : Branch) : (twist j).re = 0 := by
  simp [twist, Complex.mul_re]

theorem limitingEquation_re (j : Branch) (c : ℝ) (s : ℂ) :
    (limitingEquation j c s).re = 3 * Real.log ‖s / (c : ℂ)‖ := by
  simp [limitingEquation, Complex.mul_re, Complex.log_re]

theorem limitingPhase_branch_change (j k : Branch) (c : ℝ) (s : ℂ) :
    limitingPhase j c s = limitingPhase k c s + s * (twist j - twist k) := by
  simp only [limitingPhase, limitingEquation]
  ring

theorem saddle_one_coordinates (c : ℝ) :
    (c : ℂ) * rho .one = ((-c / 2 : ℝ) : ℂ) - ((Real.sqrt 3 * c / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, rho_one_re, rho_one_im]
  all_goals ring

theorem saddle_two_coordinates (c : ℝ) :
    (c : ℂ) * rho .two = ((-c / 2 : ℝ) : ℂ) + ((Real.sqrt 3 * c / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, rho_two_re, rho_two_im]
  all_goals ring

theorem limitingPhase_one_at_two_re {c : ℝ} (hc : 0 < c) :
    (limitingPhase .one c ((c : ℂ) * rho .two)).re = 3 * c / 2 - 2 * Real.pi * Real.sqrt 3 * c := by
  rw [limitingPhase_branch_change .one .two, Complex.add_re, limitingPhase_two_saddle_re hc,
    twist_one, twist_two]
  simp [Complex.mul_re, Complex.mul_im, rho_two_re, rho_two_im]
  ring

theorem limitingPhase_two_at_one_re {c : ℝ} (hc : 0 < c) :
    (limitingPhase .two c ((c : ℂ) * rho .one)).re = 3 * c / 2 - 2 * Real.pi * Real.sqrt 3 * c := by
  rw [limitingPhase_branch_change .two .one, Complex.add_re, limitingPhase_one_saddle_re hc,
    twist_one, twist_two]
  simp [Complex.mul_re, Complex.mul_im, rho_one_re, rho_one_im]
  ring

def branchIndex : Branch → ℕ
  | .one => 1
  | .two => 2
  | .three => 3

/-- Identification with exactly `ρⱼ = exp(-2π i j / 3)` in Lemma 8. -/
theorem rho_eq_paper (j : Branch) :
    rho j = Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (branchIndex j : ℂ) / 3) := by
  cases j
  · rw [rho]
    congr 1
    simp only [saddleAngle, branchIndex, Nat.cast_one, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  · have he : (saddleAngle .two : ℂ) * Complex.I =
        -2 * (Real.pi : ℂ) * Complex.I * 2 / 3 + 2 * (Real.pi : ℂ) * Complex.I := by
      simp only [saddleAngle, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    rw [rho, he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rfl
  · rw [rho_three]
    have he : -2 * (Real.pi : ℂ) * Complex.I * (branchIndex .three : ℂ) / 3 =
        -(2 * (Real.pi : ℂ) * Complex.I) := by
      simp only [branchIndex, Nat.cast_ofNat]
      ring
    rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

end ThisWork
