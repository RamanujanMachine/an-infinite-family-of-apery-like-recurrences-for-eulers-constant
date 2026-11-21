module
public import ThisWork.Trajectory.AffineShift
public import ThisWork.AffineGammaNorm
/-! Bounded affine Gamma errors at square-root scale. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology
theorem abs_log_norm_Gamma_affine_add_le {A R M : ℝ} (hA : 4 ≤ A) (hR : 0 < R) (hM : 0 < M)
    (hRM : 2 * R * M ≤ A / 4) {s : ℂ} (hs : ‖s‖ ≤ M) :
    |Real.log ‖Complex.Gamma ((A : ℂ) + (R : ℂ) * s)‖ -
      Real.log ‖Complex.Gamma (A : ℂ)‖ - R * s.re * Real.log A| ≤
      R * M * ((4 / A + (3 / 2 : ℝ) * ((1 + 2 * R * M) / A)) + 2 / A) := by
  let a : ℂ := (A : ℂ)
  have hr : 0 < 2 * R * M := mul_pos (mul_pos (by norm_num) hR) hM
  have hpos : ∀ z ∈ ball a (2 * R * M), 0 < z.re :=
    fun _ hz => re_pos_of_mem_ball_ofReal (by linarith : 2 * R * M < A) hz
  have hΓ : DifferentiableOn ℂ Complex.Gamma (ball a (2 * R * M)) :=
    fun z hz => (Complex.differentiableAt_Gamma z (not_neg_nat_of_mem_slitPlane
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hpos z hz))))).differentiableWithinAt
  have hne : ∀ z ∈ ball a (2 * R * M), Complex.Gamma z ≠ 0 :=
    fun z hz => Complex.Gamma_ne_zero_of_re_pos (hpos z hz)
  obtain ⟨p, hpa, hp, he⟩ := exists_normalized_log_ball (mem_ball_self hr) hΓ hne
  have hb : ∀ z ∈ ball a (2 * R * M), ‖logDeriv Complex.Gamma z - Complex.log (A : ℂ)‖ ≤
      (4 / A + (3 / 2 : ℝ) * ((1 + 2 * R * M) / A)) + 2 / A := by
    intro z hz
    have hz' : ‖z - a‖ ≤ 2 * R * M := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using ball_subset_closedBall hz
    have h := norm_digamma_affine_add_sub_log_le hA (R := 1) zero_le_one
      (by simpa only [one_mul] using hRM) hz'
    rw [show (A : ℂ) + (1 : ℝ) * (z - a) = z by dsimp [a]; ring] at h
    simpa only [one_mul, Complex.digamma_def] using h
  let x : ℂ := (A : ℂ) + (R : ℂ) * s
  have hxa : x - a = (R : ℂ) * s := by dsimp [x, a]; ring
  have hxn : ‖x - a‖ ≤ R * M := by
    rw [hxa, norm_mul, Complex.norm_of_nonneg hR.le]
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
  have hB : 0 ≤ (4 / A + (3 / 2 : ℝ) * ((1 + 2 * R * M) / A)) + 2 / A := by positivity
  have hreal := (Complex.abs_re_le_norm (p x - (x - a) * Complex.log (A : ℂ))).trans
    (hbound.trans (mul_le_mul_of_nonneg_right hxn hB))
  have hlogeq : Real.log ‖Complex.Gamma x‖ - Real.log ‖Complex.Gamma a‖ = (p x).re := by
    rw [he x hx, norm_mul, Complex.norm_exp,
      Real.log_mul (norm_ne_zero_iff.mpr (hne a (mem_ball_self hr))) (Real.exp_ne_zero _), Real.log_exp]
    ring
  simp [hxa, ← Complex.ofReal_log hA0.le, Complex.mul_re] at hreal
  simpa only [← hlogeq] using hreal


private theorem sqrt_affine_error_bound {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n)
    {M : ℝ} (hM : 0 < M) :
    sqrtScale n * M * (4 / (α * n) + (3 / 2 : ℝ) * ((1 + 2 * sqrtScale n * M) / (α * n)) +
      2 / (α * n)) ≤ M * ((11 + 6 * M) / (2 * α) + 2 / α) := by
  have hR := sqrtScale_pos (show 0 < n by omega)
  have h₀ := affineError_le_inv_sqrtScale hα hn (2 * M)
  have h₁ : 2 / (α * n) ≤ (2 / α) * (1 / sqrtScale n) := by
    have h := mul_le_mul_of_nonneg_left (inv_nat_le_inv_sqrtScale hn)
      (show 0 ≤ 2 / α by positivity)
    convert h using 1
    field_simp
  have hb : 4 / (α * n) + (3 / 2 : ℝ) * ((1 + 2 * sqrtScale n * M) / (α * n)) +
      2 / (α * n) ≤ ((11 + 6 * M) / (2 * α) + 2 / α) / sqrtScale n := by
    convert add_le_add h₀ h₁ using 1 <;> ring
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ sqrtScale n * M)).trans_eq (by
    field_simp)

theorem uniform_log_norm_Gamma_sqrt_affine {α M : ℝ} (hα : 0 < α) (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M →
      |Real.log ‖Complex.Gamma ((α : ℂ) * n - (sqrtScale n : ℂ) * s + 1)‖ -
        Real.log ‖Complex.Gamma ((α * n + 1 : ℝ) : ℂ)‖ +
          sqrtScale n * s.re * Real.log (α * n)| ≤ C ∧
      |Real.log ‖Complex.Gamma ((α : ℂ) * n + (sqrtScale n : ℂ) * s)‖ -
        Real.log ‖Complex.Gamma ((α * n : ℝ) : ℂ)‖ -
          sqrtScale n * s.re * Real.log (α * n)| ≤ C := by
  refine ⟨M * ((11 + 6 * M) / (2 * α) + 2 / α), by positivity, ?_⟩
  filter_upwards [eventually_right_factor_conditions hα (2 * M), eventually_ge_atTop (1 : ℕ)]
    with n hn hn₁ s hs
  have hR := sqrtScale_pos (show 0 < n by omega)
  have hRM : 2 * sqrtScale n * M ≤ α * n / 4 := by nlinarith [hn.2]
  have h₀ := abs_log_norm_Gamma_affine_sub_le hn.1 hR hM hRM hs
  have h₁ := abs_log_norm_Gamma_affine_add_le hn.1 hR hM hRM hs
  rw [Complex.ofReal_mul, Complex.ofReal_natCast] at h₀ h₁
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  refine ⟨h₀.trans ?_, h₁.trans (sqrt_affine_error_bound hα hn₁ hM)⟩
  exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity : 0 ≤ 2 / (α * n)))
    (by positivity : 0 ≤ sqrtScale n * M)).trans (sqrt_affine_error_bound hα hn₁ hM)

end ThisWork.Trajectory
