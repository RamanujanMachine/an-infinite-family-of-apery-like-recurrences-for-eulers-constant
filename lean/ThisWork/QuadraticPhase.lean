module

public import ThisWork.CenteredPhase
public import ThisWork.ParabolicContour
public import ThisWork.TaylorTools

/-! Uniform quadratic expansions of the compact arbitrary-rank phase family. -/

@[expose] public section
namespace ThisWork.CompactSaddleFamily

open Set Filter Metric
open scoped Topology OnePoint

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}
    (S : CompactSaddleFamily r A z j ζ δ)

noncomputable def phaseCoefficients (n : ℕ) (q : OnePoint ℕ) : ℂ :=
  iteratedDeriv (n + 2) (fun t => S.phase t q) 0 / ((n + 2).factorial : ℂ)

theorem phase_expansion (q : OnePoint ℕ) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => S.phaseCoefficients n q * (t - 0) ^ (2 + n)) (S.phase t q - S.phase 0 q) := by
  simpa only [phaseCoefficients, sub_zero, phase_zero] using
    Analytic.hasSum_quadratic_of_analytic
      ((S.differentiableOn_phase q).analyticAt (ball_mem_nhds 0 (half_pos S.radius_pos)))
      (S.phase_zero q) (S.phase_simple_saddle q).1

theorem phaseCoefficients_zero_ne (q : OnePoint ℕ) : S.phaseCoefficients 0 q ≠ 0 := by
  simpa [phaseCoefficients, iteratedDeriv_succ, iteratedDeriv_zero] using
    div_ne_zero (S.phase_simple_saddle q).2 (show (2 : ℂ) ≠ 0 by norm_num)

theorem continuous_phaseCoefficients (n : ℕ) : Continuous (S.phaseCoefficients n) := by
  change Continuous (fun q => iteratedDeriv (n + 2) (fun t => S.phase t q) 0 / ((n + 2).factorial : ℂ))
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    Neuschel.continuous_coeff_family (n + 2) isOpen_ball (mem_ball_self (half_pos S.radius_pos))
      S.continuous_phase S.differentiableOn_phase
      (fun q => ((S.differentiableOn_phase q).analyticAt
        (ball_mem_nhds 0 (half_pos S.radius_pos))).hasFPowerSeriesAt)

theorem phase_second_deriv (q : OnePoint ℕ) :
    deriv (deriv (fun t => S.phase t q)) 0 = -deriv (fun t => S.shiftedEquation t q) 0 := by
  have he : deriv (fun t => S.phase t q) =ᶠ[𝓝 (0 : ℂ)] fun t => -S.shiftedEquation t q :=
    Filter.mem_of_superset (ball_mem_nhds 0 (half_pos S.radius_pos))
      (fun t ht => (S.hasDerivAt_phase ht q).deriv)
  exact he.deriv_eq.trans (deriv.fun_neg)

theorem phaseCoefficients_zero_limit (hζ : ζ ∈ Complex.slitPlane) :
    S.phaseCoefficients 0 ∞ = -(r : ℂ) / (2 * ζ) := by
  have he : (fun t => S.shiftedEquation t ∞) = (fun t => limitingEquation r A z j (t + ζ)) :=
    funext S.shiftedEquation_limit
  simp only [phaseCoefficients, zero_add, show 2 = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_zero, S.phase_second_deriv, he,
    deriv_comp_add_const, zero_add, (hasDerivAt_limitingEquation r A z j hζ).deriv]
  norm_num [Nat.factorial]
  ring

theorem parabolic_quadratic_coefficient {a b : ℝ} (ha : 0 < a)
    (S : CompactSaddleFamily r A z j (parabolicPoint a b) δ) :
    S.phaseCoefficients 0 ∞ * (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2 = 2 * (r : ℂ) := by
  rw [S.phaseCoefficients_zero_limit (parabolicPoint_mem_slitPlane ha b)]
  calc
    _ = (-1 / 2 : ℂ) * (((r : ℂ) / parabolicPoint a b) *
        (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2) := by ring
    _ = _ := by rw [parabolic_gaussian_coefficient r ha b]; ring

noncomputable def quadraticFactor : ℂ → OnePoint ℕ → ℂ := Neuschel.phaseQuotient 2 0 S.phase

theorem quadraticFactor_regular :
    ContinuousOn (Function.uncurry S.quadraticFactor) (ball 0 (δ / 2) ×ˢ univ) ∧
      ∀ q, DifferentiableOn ℂ (fun t => S.quadraticFactor t q) (ball 0 (δ / 2)) :=
  Neuschel.phaseQuotient_regular 2 isOpen_ball (mem_ball_self (half_pos S.radius_pos))
    S.continuous_phase S.differentiableOn_phase

theorem quadraticFactor_center (q : OnePoint ℕ) : S.quadraticFactor 0 q = S.phaseCoefficients 0 q := by
  apply Neuschel.phaseQuotient_center_of_expansion 2
  simpa only [phase_zero, sub_zero] using S.phase_expansion q

theorem phase_eq_quadratic (t : ℂ) (q : OnePoint ℕ) : S.phase t q = t ^ 2 * S.quadraticFactor t q := by
  have hs : ∀ᶠ u in 𝓝 (0 : ℂ), HasSum
      (fun n => S.phaseCoefficients n q * (u - 0) ^ (2 + n)) (S.phase u q) := by
    simpa only [phase_zero, sub_zero] using S.phase_expansion q
  simpa only [sub_zero, quadraticFactor] using Neuschel.eq_pow_mul_phaseQuotient_of_expansion 2 hs t

end ThisWork.CompactSaddleFamily
