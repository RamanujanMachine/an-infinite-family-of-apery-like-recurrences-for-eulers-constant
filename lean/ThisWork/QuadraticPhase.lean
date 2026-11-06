module

public import ThisWork.CenteredPhase
public import Neuschel.LocalExpansion

/-! Convergent quadratic expansions of the actual centered saddle phases. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology OnePoint

theorem hasSum_quadratic_of_analytic {p : ℂ → ℂ} (hp : AnalyticAt ℂ p 0)
    (hp0 : p 0 = 0) (hp1 : deriv p 0 = 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => (iteratedDeriv (n + 2) p 0 / ((n + 2).factorial : ℂ)) * t ^ (2 + n)) (p t) := by
  have hs := hasFPowerSeriesAt_iff'.mp hp.hasFPowerSeriesAt
  filter_upwards [hs] with t ht
  simpa [FormalMultilinearSeries.coeff_ofScalars, Finset.sum_range_succ,
    iteratedDeriv_zero, iteratedDeriv_one, hp0, hp1, smul_eq_mul,
    Nat.add_comm, mul_comm] using (hasSum_nat_add_iff' 2).mpr ht

namespace CompactSaddleFamily

noncomputable def phaseCoefficients {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (n : ℕ) (z : OnePoint ℕ) : ℂ :=
  iteratedDeriv (n + 2) (fun t => S.phase t z) 0 / ((n + 2).factorial : ℂ)

theorem phase_expansion {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => S.phaseCoefficients n z * (t - 0) ^ (2 + n)) (S.phase t z - S.phase 0 z) := by
  simpa only [phaseCoefficients, sub_zero, phase_zero] using
    hasSum_quadratic_of_analytic
      ((S.differentiableOn_phase h₁ h₂ z).analyticAt
        (ball_mem_nhds 0 (div_pos (saddleScale_pos h₁ h₂) (by norm_num))))
      (S.phase_zero z) (S.phase_simple_saddle h₁ h₂ z).1

theorem phaseCoefficients_zero_ne {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) : S.phaseCoefficients 0 z ≠ 0 := by
  simpa [phaseCoefficients, iteratedDeriv_succ, iteratedDeriv_zero] using
    div_ne_zero (S.phase_simple_saddle h₁ h₂ z).2 (show (2 : ℂ) ≠ 0 by norm_num)

theorem continuous_phaseCoefficients {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (n : ℕ) : Continuous (S.phaseCoefficients n) := by
  change Continuous (fun z => iteratedDeriv (n + 2) (fun t => S.phase t z) 0 / ((n + 2).factorial : ℂ))
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    Neuschel.continuous_coeff_family (n + 2) isOpen_ball
      (mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))
      S.continuous_phase (S.differentiableOn_phase h₁ h₂)
      (fun z => ((S.differentiableOn_phase h₁ h₂ z).analyticAt
        (ball_mem_nhds 0 (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))).hasFPowerSeriesAt)

theorem phase_second_deriv {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    deriv (deriv (fun t => S.phase t z)) 0 = -deriv (fun t => S.shiftedEquation t z) 0 := by
  have he : deriv (fun t => S.phase t z) =ᶠ[𝓝 (0 : ℂ)] fun t => -S.shiftedEquation t z :=
    Filter.mem_of_superset
      (ball_mem_nhds 0 (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))
      (fun t ht => (S.hasDerivAt_phase h₁ h₂ ht z).deriv)
  exact he.deriv_eq.trans (deriv.fun_neg)

theorem phaseCoefficients_zero_limit {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) :
    S.phaseCoefficients 0 ∞ = -3 / (2 * (saddleScale α₁ α₂ : ℂ) * rho j) := by
  have he : (fun t => S.shiftedEquation t ∞) =
      (fun t => limitingEquation j (saddleScale α₁ α₂) (t + (saddleScale α₁ α₂ : ℂ) * rho j)) :=
    funext S.shiftedEquation_limit
  simp only [phaseCoefficients, zero_add, show 2 = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_zero, S.phase_second_deriv h₁ h₂, he,
    deriv_comp_add_const, zero_add, (hasDerivAt_limitingEquation_saddle j (saddleScale_pos h₁ h₂)).deriv]
  norm_num [Nat.factorial]
  ring

noncomputable def quadraticFactor {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) : ℂ → OnePoint ℕ → ℂ :=
  Neuschel.phaseQuotient 2 0 S.phase

theorem quadraticFactor_regular {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) :
    ContinuousOn (Function.uncurry S.quadraticFactor) (ball 0 (saddleScale α₁ α₂ / 16) ×ˢ univ) ∧
      ∀ z, DifferentiableOn ℂ (fun t => S.quadraticFactor t z) (ball 0 (saddleScale α₁ α₂ / 16)) :=
  Neuschel.phaseQuotient_regular 2 isOpen_ball
    (mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))
    S.continuous_phase (S.differentiableOn_phase h₁ h₂)

theorem quadraticFactor_center {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    S.quadraticFactor 0 z = S.phaseCoefficients 0 z := by
  apply Neuschel.phaseQuotient_center_of_expansion 2
  simpa only [phase_zero, sub_zero] using S.phase_expansion h₁ h₂ z

theorem phase_eq_quadratic {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (t : ℂ) (z : OnePoint ℕ) :
    S.phase t z = t ^ 2 * S.quadraticFactor t z := by
  have hs : ∀ᶠ u in 𝓝 (0 : ℂ), HasSum
      (fun n => S.phaseCoefficients n z * (u - 0) ^ (2 + n)) (S.phase u z) := by
    simpa only [phase_zero, sub_zero] using S.phase_expansion h₁ h₂ z
  simpa only [sub_zero, quadraticFactor] using Neuschel.eq_pow_mul_phaseQuotient_of_expansion 2 hs t

end CompactSaddleFamily

noncomputable def saddleTangent : Branch → ℂ
  | .one | .two => 1
  | .three => Complex.I

@[simp] theorem norm_saddleTangent (j : Branch) : ‖saddleTangent j‖ = 1 := by
  cases j <;> simp [saddleTangent]

theorem saddleTangent_ne_zero (j : Branch) : saddleTangent j ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_saddleTangent]; norm_num)

theorem limiting_quadratic_positive {c : ℝ} (hc : 0 < c) (j : Branch) :
    0 < ((-3 / (2 * (c : ℂ) * rho j)) * saddleTangent j ^ 2).re := by
  rw [div_mul_eq_div_mul_one_div, one_div, Complex.inv_eq_conj (norm_rho j)]
  have he : (-3 / (2 * (c : ℂ))) = ((-3 / (2 * c) : ℝ) : ℂ) := by push_cast; rfl
  have hn : -3 / (2 * c) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  cases j <;> simp [saddleTangent, Complex.mul_re, rho_one_re, rho_two_re]
  all_goals
    rw [he]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    linarith

end ThisWork
