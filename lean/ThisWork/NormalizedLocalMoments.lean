module

public import ThisWork.LocalMoments

/-! Gaussian normalization and saddle-power limits for local parabolic moments. -/

@[expose] public section
namespace ThisWork.CompactSaddleFamily.LocalParabolicData

open Set Filter Metric
open scoped Topology OnePoint

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}
    {S : CompactSaddleFamily r A z j ζ δ} {v : ℂ} (D : S.LocalParabolicData v)

noncomputable def quadraticRoot (q : OnePoint ℕ) : ℂ :=
  Neuschel.leadingRoot 2 ((D.speed : ℂ) * v) (S.phaseCoefficients 0 (Analytic.parameterShift D.shift q))

noncomputable def normalizedLocalMoment (R : ℝ) (k : ℕ) (q : OnePoint ℕ) : ℂ :=
  D.quadraticRoot q * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) * D.localMoment R k q

theorem uniform_quadraticRoot_bounds (hv : v ≠ 0) :
    ∃ B ≥ 1, ∀ q, ‖D.quadraticRoot q‖ ≤ B ∧ ‖(D.quadraticRoot q)⁻¹‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := Neuschel.exists_uniform_quadratic_root_bounds
    (S.continuous_phaseCoefficients 0) S.phaseCoefficients_zero_ne
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr D.speed_pos.ne') hv)
  exact ⟨B, hB, fun q => hb (Analytic.parameterShift D.shift q)⟩

theorem normalized_local_moment_error (hv : v ≠ 0) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ q,
      ‖D.normalizedLocalMoment R k q - S.saddle (Analytic.parameterShift D.shift q) ^ k‖ ≤
        C * R ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := D.uniform_quadraticRoot_bounds hv
  obtain ⟨C, hC, hc⟩ := D.local_moment_leading_estimate hv k
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨B * C / Real.Gamma (1 / 2 : ℝ), by positivity, ?_⟩
  filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with R hR hR0 q
  have hroot : D.quadraticRoot q ≠ 0 := Neuschel.leadingRoot_ne_zero 2
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr D.speed_pos.ne') hv) _
  have hp : 0 < R ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hR0 _
  have hcancel : D.quadraticRoot q * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) *
      (S.saddle (Analytic.parameterShift D.shift q) ^ k * (D.quadraticRoot q)⁻¹ *
        ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      S.saddle (Analytic.parameterShift D.shift q) ^ k := by
    push_cast
    field_simp [hroot, Complex.ofReal_ne_zero.mpr hG.ne', Complex.ofReal_ne_zero.mpr hp.ne']
    exact mul_div_cancel_left₀ _
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne') (Complex.ofReal_ne_zero.mpr hG.ne'))
  have he : D.normalizedLocalMoment R k q - S.saddle (Analytic.parameterShift D.shift q) ^ k =
      (D.quadraticRoot q * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)) *
      (D.localMoment R k q - S.saddle (Analytic.parameterShift D.shift q) ^ k * (D.quadraticRoot q)⁻¹ *
        ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
    rw [mul_sub, hcancel]
    rfl
  rw [he, norm_mul, norm_mul, Complex.norm_of_nonneg (div_pos hp hG).le]
  calc
    _ ≤ (B * (R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ))) * (C * R ^ (-1 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hb q).1 (div_pos hp hG).le)
        (hR q) (norm_nonneg _) (by positivity)
    _ = (B * C / Real.Gamma (1 / 2 : ℝ)) * (R ^ (1 / 2 : ℝ) * R ^ (-1 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hR0]; norm_num

theorem normalizedLocalMoment_tendsto (hr : 1 < r) (hv : v ≠ 0) (k : ℕ) :
    Tendsto (fun n : ℕ => D.normalizedLocalMoment (largeScale r (n + D.shift + S.firstIndex)) k n)
      atTop (𝓝 (ζ ^ k)) := by
  have hscale : Tendsto (fun n : ℕ => largeScale r (n + D.shift + S.firstIndex)) atTop atTop :=
    (largeScale_tendsto hr).comp ((tendsto_add_atTop_nat S.firstIndex).comp (tendsto_add_atTop_nat D.shift))
  have hσ : Tendsto (fun n : ℕ => S.saddle (Analytic.parameterShift D.shift n)) atTop (𝓝 ζ) := by
    simpa only [Analytic.parameterShift_nat, S.saddle_limit, Function.comp_def] using
      ((OnePoint.continuous_iff_from_nat S.saddle).mp S.saddle.continuous).comp (tendsto_add_atTop_nat D.shift)
  obtain ⟨C, _, hc⟩ := D.normalized_local_moment_error hv k
  have he : Tendsto (fun n : ℕ =>
      D.normalizedLocalMoment (largeScale r (n + D.shift + S.firstIndex)) k n -
        S.saddle (Analytic.parameterShift D.shift n) ^ k) atTop (𝓝 0) :=
    squeeze_zero_norm' ((hscale.eventually hc).mono (fun n hn => hn n))
      (by simpa only [mul_zero, Function.comp_def] using
        ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp hscale).const_mul C)
  simpa only [sub_add_cancel, zero_add] using he.add (hσ.pow k)

end ThisWork.CompactSaddleFamily.LocalParabolicData
