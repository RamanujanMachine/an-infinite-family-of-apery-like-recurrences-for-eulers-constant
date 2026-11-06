module

public import ThisWork.GammaNorm
public import ThisWork.AffineDigamma
public import ThisWork.SaddleApproximation

/-! Logarithmic norm estimates for the shifted right-hand Gamma factors. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem re_pos_of_mem_ball_ofReal {a r : ℝ} (hr : r < a) {z : ℂ}
    (hz : z ∈ ball (a : ℂ) r) : 0 < z.re := by
  have hd : ‖(a : ℂ) - z‖ < r := by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have he : a - z.re ≤ ‖(a : ℂ) - z‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.re_le_norm ((a : ℂ) - z)
  linarith

theorem abs_log_norm_Gamma_affine_sub_le {A R M : ℝ} (hA : 4 ≤ A) (hR : 0 < R) (hM : 0 < M)
    (hRM : 2 * R * M ≤ A / 4) {s : ℂ} (hs : ‖s‖ ≤ M) :
    |Real.log ‖Complex.Gamma ((A : ℂ) - (R : ℂ) * s + 1)‖ -
      Real.log ‖Complex.Gamma ((A + 1 : ℝ) : ℂ)‖ + R * s.re * Real.log A| ≤
      R * M * (4 / A + (3 / 2 : ℝ) * ((1 + 2 * R * M) / A)) := by
  let a : ℂ := ((A + 1 : ℝ) : ℂ)
  have hr : 0 < 2 * R * M := mul_pos (mul_pos (by norm_num) hR) hM
  have hpos : ∀ z ∈ ball a (2 * R * M), 0 < z.re :=
    fun _ hz => re_pos_of_mem_ball_ofReal (by linarith : 2 * R * M < A + 1) hz
  have hΓ : DifferentiableOn ℂ Complex.Gamma (ball a (2 * R * M)) :=
    fun z hz => (Complex.differentiableAt_Gamma z (not_neg_nat_of_mem_slitPlane
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hpos z hz))))).differentiableWithinAt
  have hne : ∀ z ∈ ball a (2 * R * M), Complex.Gamma z ≠ 0 :=
    fun z hz => Complex.Gamma_ne_zero_of_re_pos (hpos z hz)
  obtain ⟨p, hpa, hp, he⟩ := exists_normalized_log_ball (mem_ball_self hr) hΓ hne
  have hb : ∀ z ∈ ball a (2 * R * M), ‖logDeriv Complex.Gamma z - Complex.log (A : ℂ)‖ ≤
      4 / A + (3 / 2 : ℝ) * ((1 + 2 * R * M) / A) := by
    intro z hz
    have hz' : ‖a - z‖ ≤ 2 * R * M := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using ball_subset_closedBall hz
    have h := norm_digamma_affine_sub_log_le hA (R := 1) zero_le_one
      (by simpa only [one_mul] using hRM) hz'
    rw [show (A : ℂ) - (1 : ℝ) * (a - z) + 1 = z by dsimp [a]; push_cast; ring] at h
    simpa only [one_mul, Complex.digamma_def] using h
  let x : ℂ := (A : ℂ) - (R : ℂ) * s + 1
  have hxa : x - a = -(R : ℂ) * s := by dsimp [x, a]; push_cast; ring
  have hxn : ‖x - a‖ ≤ R * M := by
    rw [hxa, norm_mul, norm_neg, Complex.norm_of_nonneg hR.le]
    exact mul_le_mul_of_nonneg_left hs hR.le
  have hx : x ∈ ball a (2 * R * M) := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hlog : DifferentiableOn ℂ (logDeriv Complex.Gamma) (ball a (2 * R * M)) := by
    convert (hΓ.deriv isOpen_ball).div hΓ hne using 1
    rfl
  have hbound := norm_primitive_sub_le_ball (mem_ball_self hr) hx hp
    (fun z _ => by simpa only [id_eq, one_mul] using
      ((hasDerivAt_id z).sub_const a).mul_const (Complex.log (A : ℂ)))
    (hlog.continuousOn.fun_sub continuousOn_const) hb
  simp only [hpa, sub_self, sub_zero, zero_mul] at hbound
  have hA0 : 0 < A := by linarith
  have hB : 0 ≤ 4 / A + (3 / 2 : ℝ) * ((1 + 2 * R * M) / A) := by positivity
  have hreal := (Complex.abs_re_le_norm (p x - (x - a) * Complex.log (A : ℂ))).trans
    (hbound.trans (mul_le_mul_of_nonneg_right hxn hB))
  have hlogeq : Real.log ‖Complex.Gamma x‖ - Real.log ‖Complex.Gamma a‖ = (p x).re := by
    rw [he x hx, norm_mul, Complex.norm_exp,
      Real.log_mul (norm_ne_zero_iff.mpr (hne a (mem_ball_self hr))) (Real.exp_ne_zero _), Real.log_exp]
    ring
  simp [hxa, ← Complex.ofReal_log hA0.le, Complex.mul_re] at hreal
  simpa only [← hlogeq] using hreal

theorem uniform_log_norm_Gamma_affine {α M : ℝ} (hα : 0 < α) (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M →
      |Real.log ‖Complex.Gamma ((α : ℂ) * n - (largeScale n : ℂ) * s + 1)‖ -
        Real.log ‖Complex.Gamma ((α * n + 1 : ℝ) : ℂ)‖ +
        largeScale n * s.re * Real.log (α * n)| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  let L := (11 + 3 * (2 * M)) / (2 * α)
  refine ⟨M * L, by dsimp only [L]; positivity, ?_⟩
  filter_upwards [eventually_right_factor_conditions hα (2 * M), eventually_ge_atTop (1 : ℕ)]
    with n hn hn₁ s hs
  have hR := largeScale_pos (show 0 < n by omega)
  have h := abs_log_norm_Gamma_affine_sub_le hn.1 hR hM (by nlinarith [hn.2]) hs
  rw [Complex.ofReal_mul, Complex.ofReal_natCast] at h
  apply h.trans
  have hB : 4 / (α * n) + (3 / 2 : ℝ) * ((1 + 2 * largeScale n * M) / (α * n)) ≤
      L * smallParameter n := by
    simpa only [L, mul_left_comm, mul_assoc] using affineError_le_smallParameter hα hn₁ (2 * M)
  calc
    _ ≤ largeScale n * M * (L * smallParameter n) :=
      mul_le_mul_of_nonneg_left hB (mul_nonneg hR.le hM.le)
    _ = M * L * (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [← largeScale_mul_smallParameter (show 0 < n by omega)]
      ring

end ThisWork
