module

public import ThisWork.Argument
public import ThisWork.QuadraticPhase

/-! Uniform positive local contour halves at the moving exact saddles. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology OnePoint

/-- Discard a finite initial segment while retaining the compact parameter space. -/
noncomputable def parameterShift (N : ℕ) : C(OnePoint ℕ, OnePoint ℕ) :=
  OnePoint.continuousMapMkNat (fun m => ((m + N : ℕ) : OnePoint ℕ)) ∞
    (((OnePoint.continuous_iff_from_nat (id : OnePoint ℕ → OnePoint ℕ)).mp continuous_id).comp
      (tendsto_add_atTop_nat N))

@[simp] theorem parameterShift_nat (N m : ℕ) : parameterShift N m = ((m + N : ℕ) : OnePoint ℕ) := rfl
@[simp] theorem parameterShift_limit (N : ℕ) : parameterShift N ∞ = ∞ := rfl

namespace CompactSaddleFamily

theorem exists_shift_quadratic_positive [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) :
    ∃ N : ℕ, ∀ z : OnePoint ℕ,
      0 < (S.phaseCoefficients 0 (parameterShift N z) * saddleTangent j ^ 2).re := by
  have hp : 0 < (S.phaseCoefficients 0 ∞ * saddleTangent j ^ 2).re := by
    rw [S.phaseCoefficients_zero_limit h₁ h₂]
    exact limiting_quadratic_positive (saddleScale_pos h₁ h₂) j
  have he : ∀ᶠ m : ℕ in atTop, 0 < (S.phaseCoefficients 0 m * saddleTangent j ^ 2).re :=
    ((OnePoint.continuous_iff_from_nat _).mp
      (Complex.continuous_re.comp ((S.continuous_phaseCoefficients h₁ h₂ 0).mul continuous_const))).eventually
        (lt_mem_nhds hp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun z => ?_⟩
  cases z with
  | infty => exact hp
  | coe m => exact hN (m + N) (Nat.le_add_left N m)

theorem exists_uniform_quadratic_neighborhood [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) :
    ∃ N : ℕ, ∃ r > 0, ball (0 : ℂ) r ⊆ ball 0 (saddleScale α₁ α₂ / 16) ∧
      ∀ t ∈ ball (0 : ℂ) r, ∀ z : OnePoint ℕ,
        0 < (S.quadraticFactor t (parameterShift N z) * saddleTangent j ^ 2).re := by
  obtain ⟨N, hN⟩ := S.exists_shift_quadratic_positive h₁ h₂
  have hc : Continuous (fun w : ℂ × OnePoint ℕ => (w.1, parameterShift N w.2)) :=
    continuous_fst.prodMk ((parameterShift N).continuous.comp continuous_snd)
  have hq := (S.quadraticFactor_regular h₁ h₂).1.comp
    (s := ball (0 : ℂ) (saddleScale α₁ α₂ / 16) ×ˢ (univ : Set (OnePoint ℕ)))
    hc.continuousOn (fun w hw => ⟨hw.1, mem_univ _⟩)
  change ContinuousOn (Function.uncurry (fun t z => S.quadraticFactor t (parameterShift N z)))
    (ball (0 : ℂ) (saddleScale α₁ α₂ / 16) ×ˢ univ) at hq
  have hV : IsOpen {w : ℂ | 0 < (w * saddleTangent j ^ 2).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.mul continuous_const))
  obtain ⟨r, hr, hrG, hb⟩ := Neuschel.exists_uniform_mapsTo_nhds isOpen_ball
    (mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num))) hq hV
    (fun z => by
      change 0 < (S.quadraticFactor 0 (parameterShift N z) * saddleTangent j ^ 2).re
      rw [S.quadraticFactor_center h₁ h₂]
      exact hN z)
  exact ⟨N, r, hr, hrG, fun t ht z => hb z ht⟩

theorem exists_uniform_tangent_positivity [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) :
    ∃ N : ℕ, ∃ r > 0, ∀ u : ℝ, |u| < r → u ≠ 0 → ∀ z : OnePoint ℕ,
      (u : ℂ) * saddleTangent j ∈ ball 0 (saddleScale α₁ α₂ / 16) ∧
      0 < (S.phase ((u : ℂ) * saddleTangent j) (parameterShift N z)).re := by
  obtain ⟨N, r, hr, hrG, hb⟩ := S.exists_uniform_quadratic_neighborhood h₁ h₂
  refine ⟨N, r, hr, fun u hu hne z => ?_⟩
  have ht : (u : ℂ) * saddleTangent j ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_saddleTangent, mul_one] using hu
  refine ⟨hrG ht, ?_⟩
  rw [S.phase_eq_quadratic h₁ h₂]
  have he : (((u : ℂ) * saddleTangent j) ^ 2 *
      S.quadraticFactor ((u : ℂ) * saddleTangent j) (parameterShift N z)).re =
      u ^ 2 * (S.quadraticFactor ((u : ℂ) * saddleTangent j) (parameterShift N z) * saddleTangent j ^ 2).re := by
    simp only [mul_pow, mul_assoc, mul_comm (saddleTangent j ^ 2), ← Complex.ofReal_pow,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact he ▸ mul_pos (sq_pos_of_ne_zero hne) (hb _ ht z)

theorem exists_local_saddle_contour_models [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) :
    ∃ N : ℕ, ∃ d > 0, ∀ e : ℝ, e = 1 ∨ e = -1 →
      Nonempty (Neuschel.LocalContourModel 2 0 (((e * d : ℝ) : ℂ) * saddleTangent j)
        (fun z => S.phaseCoefficients 0 (parameterShift N z))
        (fun t z => S.phase t (parameterShift N z)) (ball 0 (saddleScale α₁ α₂ / 16))
        (fun u : ℝ => (u : ℂ) * (((e * d : ℝ) : ℂ) * saddleTangent j))) := by
  obtain ⟨N, r, hr, hb⟩ := S.exists_uniform_tangent_positivity h₁ h₂
  refine ⟨N, r / 2, half_pos hr, fun e he => ?_⟩
  have hc : Continuous (fun w : ℂ × OnePoint ℕ => (w.1, parameterShift N w.2)) :=
    continuous_fst.prodMk ((parameterShift N).continuous.comp continuous_snd)
  have hP := S.continuous_phase.comp
    (s := ball (0 : ℂ) (saddleScale α₁ α₂ / 16) ×ˢ (univ : Set (OnePoint ℕ)))
    hc.continuousOn (fun w hw => ⟨hw.1, mem_univ _⟩)
  change ContinuousOn (Function.uncurry (fun t z => S.phase t (parameterShift N z)))
    (ball (0 : ℂ) (saddleScale α₁ α₂ / 16) ×ˢ univ) at hP
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hv : (((e * (r / 2) : ℝ) : ℂ) * saddleTangent j) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero he0 (half_pos hr).ne'))
      (saddleTangent_ne_zero j)
  have hγ : HasDerivWithinAt
      (fun u : ℝ => (u : ℂ) * (((e * (r / 2) : ℝ) : ℂ) * saddleTangent j))
      (((e * (r / 2) : ℝ) : ℂ) * saddleTangent j) (Ici 0) 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt.mul_const (((e * (r / 2) : ℝ) : ℂ) * saddleTangent j)).hasDerivWithinAt
  apply Neuschel.exists_localContourModel isOpen_ball
    (mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num))) (by decide) hP
    (fun z => S.differentiableOn_phase h₁ h₂ (parameterShift N z))
    (fun z => S.phase_expansion h₁ h₂ (parameterShift N z))
    (fun z => S.phaseCoefficients_zero_ne h₁ h₂ (parameterShift N z)) hγ (by simp) hv
  intro s hs z
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have hu : |e * (r / 2) * s| < r := by
    rw [abs_mul, abs_mul, heabs, abs_of_pos (half_pos hr), abs_of_pos hs.1]
    nlinarith [mul_lt_mul_of_pos_left hs.2 hr]
  have harg : (s : ℂ) * (((e * (r / 2) : ℝ) : ℂ) * saddleTangent j) =
      ((e * (r / 2) * s : ℝ) : ℂ) * saddleTangent j := by push_cast; ring
  simpa only [phase_zero, sub_zero, harg] using
    (hb (e * (r / 2) * s) hu
      (mul_ne_zero (mul_ne_zero he0 (half_pos hr).ne') hs.1.ne') z).2

end CompactSaddleFamily

end ThisWork.Analytic
