module

public import ThisWork.Argument
public import ThisWork.LocalSaddleExpansion

/-! Normalized local power moments converge to the powers of the limiting saddle. -/

@[expose] public section

namespace ThisWork.Analytic.CompactSaddleFamily.LocalSaddleData


open Set Filter Metric
open scoped Topology OnePoint

noncomputable def quadraticRoot [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (z : OnePoint ℕ) : ℂ :=
  Neuschel.leadingRoot 2 D.velocity (S.phaseCoefficients 0 (parameterShift D.shift z))

noncomputable def normalizedLocalMoment [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (R : ℝ) (k : ℕ) (z : OnePoint ℕ) : ℂ :=
  D.quadraticRoot z * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) * D.localMoment R k z

theorem uniform_quadraticRoot_bounds [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ B ≥ 1, ∀ z, ‖D.quadraticRoot z‖ ≤ B ∧ ‖(D.quadraticRoot z)⁻¹‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := Neuschel.exists_uniform_quadratic_root_bounds
    (S.continuous_phaseCoefficients h₁ h₂ 0) (S.phaseCoefficients_zero_ne h₁ h₂) D.velocity_ne_zero
  exact ⟨B, hB, fun z => hb (parameterShift D.shift z)⟩

theorem normalized_local_moment_error [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ z,
      ‖D.normalizedLocalMoment R k z - S.saddle (parameterShift D.shift z) ^ k‖ ≤
        C * R ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := D.uniform_quadraticRoot_bounds h₁ h₂
  obtain ⟨C, hC, hc⟩ := D.local_moment_leading_estimate h₁ h₂ k
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨B * C / Real.Gamma (1 / 2 : ℝ), by positivity, ?_⟩
  filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with R hR hR0 z
  have hroot : D.quadraticRoot z ≠ 0 := Neuschel.leadingRoot_ne_zero 2 D.velocity_ne_zero _
  have hp : 0 < R ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hR0 _
  have hcancel : D.quadraticRoot z * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) *
      (S.saddle (parameterShift D.shift z) ^ k * (D.quadraticRoot z)⁻¹ *
        ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      S.saddle (parameterShift D.shift z) ^ k := by
    push_cast
    field_simp [hroot, Complex.ofReal_ne_zero.mpr hG.ne', Complex.ofReal_ne_zero.mpr hp.ne']
    exact mul_div_cancel_left₀ _
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne') (Complex.ofReal_ne_zero.mpr hG.ne'))
  have he : D.normalizedLocalMoment R k z - S.saddle (parameterShift D.shift z) ^ k =
      (D.quadraticRoot z * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)) *
      (D.localMoment R k z - S.saddle (parameterShift D.shift z) ^ k * (D.quadraticRoot z)⁻¹ *
        ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
    rw [mul_sub, hcancel]
    rfl
  rw [he, norm_mul, norm_mul, Complex.norm_of_nonneg (div_pos hp hG).le]
  calc
    _ ≤ (B * (R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ))) * (C * R ^ (-1 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hb z).1 (div_pos hp hG).le)
        (hR z) (norm_nonneg _) (by positivity)
    _ = (B * C / Real.Gamma (1 / 2 : ℝ)) * (R ^ (1 / 2 : ℝ) * R ^ (-1 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hR0]; norm_num

theorem normalizedLocalMoment_tendsto [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (k : ℕ) :
    Tendsto (fun m : ℕ => D.normalizedLocalMoment (largeScale (m + D.shift + S.firstIndex)) k m)
      atTop (𝓝 (((saddleScale α₁ α₂ : ℂ) * rho j) ^ k)) := by
  have hscale : Tendsto (fun m : ℕ => largeScale (m + D.shift + S.firstIndex)) atTop atTop :=
    largeScale_tendsto.comp ((tendsto_add_atTop_nat S.firstIndex).comp (tendsto_add_atTop_nat D.shift))
  have hσ : Tendsto (fun m : ℕ => S.saddle (parameterShift D.shift m)) atTop
      (𝓝 ((saddleScale α₁ α₂ : ℂ) * rho j)) := by
    simpa only [parameterShift_nat, S.saddle_limit, Function.comp_def] using
      ((OnePoint.continuous_iff_from_nat S.saddle).mp S.saddle.continuous).comp (tendsto_add_atTop_nat D.shift)
  obtain ⟨C, _, hc⟩ := D.normalized_local_moment_error h₁ h₂ k
  have he : Tendsto (fun m : ℕ =>
      D.normalizedLocalMoment (largeScale (m + D.shift + S.firstIndex)) k m -
        S.saddle (parameterShift D.shift m) ^ k) atTop (𝓝 0) :=
    squeeze_zero_norm' ((hscale.eventually hc).mono (fun m hm => hm m))
      (by simpa only [mul_zero, Function.comp_def] using
        ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp hscale).const_mul C)
  simpa only [sub_add_cancel, zero_add] using he.add (hσ.pow k)

end ThisWork.Analytic.CompactSaddleFamily.LocalSaddleData
