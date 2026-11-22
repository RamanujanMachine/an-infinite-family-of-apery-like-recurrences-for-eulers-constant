module

public import ThisWork.HigherRank.ParabolicPhase

/-! Every off-cut saddle has the parabolic coordinates used by the contour
estimates. The coordinates remain symbolic in the saddle radius and angle. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set

theorem exists_parabolic_coordinates {c θ : ℝ} (hc : 0 < c)
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    ∃ a > 0, ∃ b : ℝ, a ^ 2 + b ^ 2 = c ∧
      2 * Real.arctan (b / a) = θ ∧ parabolicPoint a b = (c : ℂ) * Phase.rho θ := by
  let w : ℂ := (Real.sqrt c : ℂ) * Phase.rho (θ / 2)
  have ha : 0 < w.re := by
    have hcos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    simpa [w, Phase.rho, Complex.mul_re, Complex.mul_im, Complex.exp_re] using
      mul_pos (Real.sqrt_pos.mpr hc) hcos
  have hρ : Phase.rho (θ / 2) ^ 2 = Phase.rho θ := by
    rw [Phase.rho, pow_two, ← Complex.exp_add]
    unfold Phase.rho
    congr 1
    push_cast
    ring
  have hw : w ^ 2 = (c : ℂ) * Phase.rho θ := by
    dsimp only [w]
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hc.le, hρ]
  have hp : parabolicPoint w.re w.im = w ^ 2 := by
    rw [parabolicPoint, Complex.re_add_im]
  have hn : ‖w‖ ^ 2 = c := by
    simp [w, Phase.rho, Complex.norm_exp, Complex.mul_re, Real.sq_sqrt hc.le]
  have hcoords : w.re ^ 2 + w.im ^ 2 = c := by
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    nlinarith
  have hl := congrArg Complex.im (log_parabolicPoint ha w.im)
  have hnρ : Phase.rho θ ≠ 0 := Complex.exp_ne_zero _
  rw [hp, hw, Complex.log_ofReal_mul hc hnρ, Phase.log_rho hθ] at hl
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
    Complex.log_im] at hl
  rw [arg_right_halfplane ha] at hl
  norm_num at hl
  exact ⟨w.re, ha, w.im, hcoords, hl.symm, hp.trans hw⟩

end ThisWork.HigherRank
