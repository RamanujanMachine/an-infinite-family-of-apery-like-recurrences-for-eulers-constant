module

public import ThisWork.LocalSaddleExpansion

/-! A reusable compact family of centered nondegenerate saddle equations. -/

@[expose] public section
namespace ThisWork.Analytic
open Set Filter Metric MeasureTheory
open scoped Topology OnePoint

structure QuadraticSaddleFamily where
  saddle : C(OnePoint ℕ, ℂ)
  radius : ℝ
  radius_pos : 0 < radius
  equation : ℂ → OnePoint ℕ → ℂ
  continuous_equation : ContinuousOn (Function.uncurry equation) (ball 0 radius ×ˢ univ)
  holomorphic_equation : ∀ z, DifferentiableOn ℂ (fun t => equation t z) (ball 0 radius)
  equation_zero : ∀ z, equation 0 z = 0
  equation_simple : ∀ z, deriv (fun t => equation t z) 0 ≠ 0
  tangent : ℂ
  norm_tangent : ‖tangent‖ = 1
  positive_limit : 0 < ((-deriv (fun t => equation t ∞) 0 / 2) * tangent ^ 2).re

namespace QuadraticSaddleFamily

theorem tangent_ne_zero (S : QuadraticSaddleFamily) : S.tangent ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [S.norm_tangent]; norm_num)

noncomputable def phase (S : QuadraticSaddleFamily) (t : ℂ) (z : OnePoint ℕ) : ℂ :=
  -Neuschel.segmentIntegral (fun u => S.equation u z) 0 t

theorem continuous_phase (S : QuadraticSaddleFamily) :
    ContinuousOn (Function.uncurry S.phase) (ball 0 S.radius ×ˢ univ) :=
  (continuousOn_segmentIntegral_family S.continuous_equation).neg

theorem hasDerivAt_phase (S : QuadraticSaddleFamily) {t : ℂ}
    (ht : t ∈ ball 0 S.radius) (z : OnePoint ℕ) :
    HasDerivAt (fun u => S.phase u z) (-S.equation t z) t :=
  (hasDerivAt_segmentIntegral_ball S.radius_pos (S.holomorphic_equation z) ht).neg

@[simp] theorem phase_zero (S : QuadraticSaddleFamily) (z : OnePoint ℕ) : S.phase 0 z = 0 := by
  simp only [phase, Neuschel.segmentIntegral, sub_self, zero_mul, intervalIntegral.integral_zero, neg_zero]

theorem differentiableOn_phase (S : QuadraticSaddleFamily) (z : OnePoint ℕ) :
    DifferentiableOn ℂ (fun t => S.phase t z) (ball 0 S.radius) :=
  fun _ ht => (S.hasDerivAt_phase ht z).differentiableAt.differentiableWithinAt

theorem phase_simple_saddle (S : QuadraticSaddleFamily) (z : OnePoint ℕ) :
    deriv (fun t => S.phase t z) 0 = 0 ∧ deriv (deriv (fun t => S.phase t z)) 0 ≠ 0 :=
  ThisWork.Analytic.phase_simple_saddle (mem_ball_self S.radius_pos)
    (fun _ ht => S.hasDerivAt_phase ht z) (S.equation_zero z) (S.equation_simple z)
noncomputable def phaseCoefficients
    (S : QuadraticSaddleFamily) (n : ℕ) (z : OnePoint ℕ) : ℂ :=
  iteratedDeriv (n + 2) (fun t => S.phase t z) 0 / ((n + 2).factorial : ℂ)

theorem phase_expansion
    (S : QuadraticSaddleFamily) (z : OnePoint ℕ) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => S.phaseCoefficients n z * (t - 0) ^ (2 + n)) (S.phase t z - S.phase 0 z) := by
  simpa only [phaseCoefficients, sub_zero, phase_zero] using
    hasSum_quadratic_of_analytic
      ((S.differentiableOn_phase z).analyticAt
        (ball_mem_nhds 0 S.radius_pos))
      (S.phase_zero z) (S.phase_simple_saddle z).1

theorem phaseCoefficients_zero_ne
    (S : QuadraticSaddleFamily) (z : OnePoint ℕ) : S.phaseCoefficients 0 z ≠ 0 := by
  simpa [phaseCoefficients, iteratedDeriv_succ, iteratedDeriv_zero] using
    div_ne_zero (S.phase_simple_saddle z).2 (show (2 : ℂ) ≠ 0 by norm_num)

theorem continuous_phaseCoefficients
    (S : QuadraticSaddleFamily) (n : ℕ) : Continuous (S.phaseCoefficients n) := by
  change Continuous (fun z => iteratedDeriv (n + 2) (fun t => S.phase t z) 0 / ((n + 2).factorial : ℂ))
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    Neuschel.continuous_coeff_family (n + 2) isOpen_ball
      (mem_ball_self S.radius_pos)
      S.continuous_phase (S.differentiableOn_phase)
      (fun z => ((S.differentiableOn_phase z).analyticAt
        (ball_mem_nhds 0 S.radius_pos)).hasFPowerSeriesAt)

theorem phase_second_deriv
    (S : QuadraticSaddleFamily) (z : OnePoint ℕ) :
    deriv (deriv (fun t => S.phase t z)) 0 = -deriv (fun t => S.equation t z) 0 := by
  have he : deriv (fun t => S.phase t z) =ᶠ[𝓝 (0 : ℂ)] fun t => -S.equation t z :=
    Filter.mem_of_superset
      (ball_mem_nhds 0 S.radius_pos)
      (fun t ht => (S.hasDerivAt_phase ht z).deriv)
  exact he.deriv_eq.trans (deriv.fun_neg)

noncomputable def quadraticFactor
    (S : QuadraticSaddleFamily) : ℂ → OnePoint ℕ → ℂ :=
  Neuschel.phaseQuotient 2 0 S.phase

theorem quadraticFactor_regular
    (S : QuadraticSaddleFamily) :
    ContinuousOn (Function.uncurry S.quadraticFactor) (ball 0 (S.radius) ×ˢ univ) ∧
      ∀ z, DifferentiableOn ℂ (fun t => S.quadraticFactor t z) (ball 0 (S.radius)) :=
  Neuschel.phaseQuotient_regular 2 isOpen_ball
    (mem_ball_self S.radius_pos)
    S.continuous_phase (S.differentiableOn_phase)

theorem quadraticFactor_center
    (S : QuadraticSaddleFamily) (z : OnePoint ℕ) :
    S.quadraticFactor 0 z = S.phaseCoefficients 0 z := by
  apply Neuschel.phaseQuotient_center_of_expansion 2
  simpa only [phase_zero, sub_zero] using S.phase_expansion z

theorem phase_eq_quadratic
    (S : QuadraticSaddleFamily) (t : ℂ) (z : OnePoint ℕ) :
    S.phase t z = t ^ 2 * S.quadraticFactor t z := by
  have hs : ∀ᶠ u in 𝓝 (0 : ℂ), HasSum
      (fun n => S.phaseCoefficients n z * (u - 0) ^ (2 + n)) (S.phase u z) := by
    simpa only [phase_zero, sub_zero] using S.phase_expansion z
  simpa only [sub_zero, quadraticFactor] using Neuschel.eq_pow_mul_phaseQuotient_of_expansion 2 hs t


theorem exists_shift_quadratic_positive
    (S : QuadraticSaddleFamily) :
    ∃ N : ℕ, ∀ z : OnePoint ℕ,
      0 < (S.phaseCoefficients 0 (parameterShift N z) * S.tangent ^ 2).re := by
  have hp : 0 < (S.phaseCoefficients 0 ∞ * S.tangent ^ 2).re := by
    simpa only [phaseCoefficients, zero_add, show 2 = 1 + 1 from rfl,
      iteratedDeriv_succ, iteratedDeriv_zero, S.phase_second_deriv,
      show ((1 + 1 : ℕ).factorial : ℂ) = 2 by norm_num] using S.positive_limit
  have he : ∀ᶠ m : ℕ in atTop, 0 < (S.phaseCoefficients 0 m * S.tangent ^ 2).re :=
    ((OnePoint.continuous_iff_from_nat _).mp
      (Complex.continuous_re.comp ((S.continuous_phaseCoefficients 0).mul continuous_const))).eventually
        (lt_mem_nhds hp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun z => ?_⟩
  cases z with
  | infty => exact hp
  | coe m => exact hN (m + N) (Nat.le_add_left N m)

theorem exists_uniform_quadratic_neighborhood (S : QuadraticSaddleFamily) :
    ∃ N : ℕ, ∃ r > 0, ball (0 : ℂ) r ⊆ ball 0 (S.radius) ∧
      ∀ t ∈ ball (0 : ℂ) r, ∀ z : OnePoint ℕ,
        0 < (S.quadraticFactor t (parameterShift N z) * S.tangent ^ 2).re := by
  obtain ⟨N, hN⟩ := S.exists_shift_quadratic_positive
  have hc : Continuous (fun w : ℂ × OnePoint ℕ => (w.1, parameterShift N w.2)) :=
    continuous_fst.prodMk ((parameterShift N).continuous.comp continuous_snd)
  have hq := (S.quadraticFactor_regular).1.comp
    (s := ball (0 : ℂ) (S.radius) ×ˢ (univ : Set (OnePoint ℕ)))
    hc.continuousOn (fun w hw => ⟨hw.1, mem_univ _⟩)
  change ContinuousOn (Function.uncurry (fun t z => S.quadraticFactor t (parameterShift N z)))
    (ball (0 : ℂ) (S.radius) ×ˢ univ) at hq
  have hV : IsOpen {w : ℂ | 0 < (w * S.tangent ^ 2).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.mul continuous_const))
  obtain ⟨r, hr, hrG, hb⟩ := Neuschel.exists_uniform_mapsTo_nhds isOpen_ball
    (mem_ball_self S.radius_pos) hq hV
    (fun z => by
      change 0 < (S.quadraticFactor 0 (parameterShift N z) * S.tangent ^ 2).re
      rw [S.quadraticFactor_center]
      exact hN z)
  exact ⟨N, r, hr, hrG, fun t ht z => hb z ht⟩

theorem exists_uniform_tangent_positivity (S : QuadraticSaddleFamily) :
    ∃ N : ℕ, ∃ r > 0, ∀ u : ℝ, |u| < r → u ≠ 0 → ∀ z : OnePoint ℕ,
      (u : ℂ) * S.tangent ∈ ball 0 (S.radius) ∧
      0 < (S.phase ((u : ℂ) * S.tangent) (parameterShift N z)).re := by
  obtain ⟨N, r, hr, hrG, hb⟩ := S.exists_uniform_quadratic_neighborhood
  refine ⟨N, r, hr, fun u hu hne z => ?_⟩
  have ht : (u : ℂ) * S.tangent ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      S.norm_tangent, mul_one] using hu
  refine ⟨hrG ht, ?_⟩
  rw [S.phase_eq_quadratic]
  have he : (((u : ℂ) * S.tangent) ^ 2 *
      S.quadraticFactor ((u : ℂ) * S.tangent) (parameterShift N z)).re =
      u ^ 2 * (S.quadraticFactor ((u : ℂ) * S.tangent) (parameterShift N z) * S.tangent ^ 2).re := by
    simp only [mul_pow, mul_assoc, mul_comm (S.tangent ^ 2), ← Complex.ofReal_pow,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact he ▸ mul_pos (sq_pos_of_ne_zero hne) (hb _ ht z)

theorem exists_local_saddle_contour_models (S : QuadraticSaddleFamily) :
    ∃ N : ℕ, ∃ d > 0, ∀ e : ℝ, e = 1 ∨ e = -1 →
      Nonempty (Neuschel.LocalContourModel 2 0 (((e * d : ℝ) : ℂ) * S.tangent)
        (fun z => S.phaseCoefficients 0 (parameterShift N z))
        (fun t z => S.phase t (parameterShift N z)) (ball 0 (S.radius))
        (fun u : ℝ => (u : ℂ) * (((e * d : ℝ) : ℂ) * S.tangent))) := by
  obtain ⟨N, r, hr, hb⟩ := S.exists_uniform_tangent_positivity
  refine ⟨N, r / 2, half_pos hr, fun e he => ?_⟩
  have hc : Continuous (fun w : ℂ × OnePoint ℕ => (w.1, parameterShift N w.2)) :=
    continuous_fst.prodMk ((parameterShift N).continuous.comp continuous_snd)
  have hP := S.continuous_phase.comp
    (s := ball (0 : ℂ) (S.radius) ×ˢ (univ : Set (OnePoint ℕ)))
    hc.continuousOn (fun w hw => ⟨hw.1, mem_univ _⟩)
  change ContinuousOn (Function.uncurry (fun t z => S.phase t (parameterShift N z)))
    (ball (0 : ℂ) (S.radius) ×ˢ univ) at hP
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hv : (((e * (r / 2) : ℝ) : ℂ) * S.tangent) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero he0 (half_pos hr).ne'))
      (S.tangent_ne_zero)
  have hγ : HasDerivWithinAt
      (fun u : ℝ => (u : ℂ) * (((e * (r / 2) : ℝ) : ℂ) * S.tangent))
      (((e * (r / 2) : ℝ) : ℂ) * S.tangent) (Ici 0) 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt.mul_const (((e * (r / 2) : ℝ) : ℂ) * S.tangent)).hasDerivWithinAt
  apply Neuschel.exists_localContourModel isOpen_ball
    (mem_ball_self S.radius_pos) (by decide) hP
    (fun z => S.differentiableOn_phase (parameterShift N z))
    (fun z => S.phase_expansion (parameterShift N z))
    (fun z => S.phaseCoefficients_zero_ne (parameterShift N z)) hγ (by simp) hv
  intro s hs z
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have hu : |e * (r / 2) * s| < r := by
    rw [abs_mul, abs_mul, heabs, abs_of_pos (half_pos hr), abs_of_pos hs.1]
    nlinarith [mul_lt_mul_of_pos_left hs.2 hr]
  have harg : (s : ℂ) * (((e * (r / 2) : ℝ) : ℂ) * S.tangent) =
      ((e * (r / 2) * s : ℝ) : ℂ) * S.tangent := by push_cast; ring
  simpa only [phase_zero, sub_zero, harg] using
    (hb (e * (r / 2) * s) hu
      (mul_ne_zero (mul_ne_zero he0 (half_pos hr).ne') hs.1.ne') z).2


end QuadraticSaddleFamily
end ThisWork.Analytic
