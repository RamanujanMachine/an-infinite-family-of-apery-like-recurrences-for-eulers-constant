module

public import ThisWork.Argument
public import ThisWork.FullWindowRemainder
public import ThisWork.NormalizedLocalMoments

/-! Normalized power moments of the complete actual Hankel integrals. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology OnePoint

theorem norm_normalized_remainder_le {A K H L : ℂ} {C E : ℝ} (hK : K ≠ 0)
    (hrem : ‖H - K * L‖ ≤ C * ‖K‖ * E) :
    ‖A * K⁻¹ * H - A * L‖ ≤ ‖A‖ * C * E := by
  have hc : A * K⁻¹ * (K * L) = A * L := by
    calc
      _ = A * (K⁻¹ * K) * L := by ring
      _ = _ := by rw [inv_mul_cancel₀ hK, mul_one]
  have he : A * K⁻¹ * H - A * L = A * K⁻¹ * (H - K * L) := by rw [mul_sub, hc]
  rw [he, norm_mul, norm_mul]
  calc
    _ ≤ (‖A‖ * ‖K⁻¹‖) * (C * ‖K‖ * E) :=
      mul_le_mul_of_nonneg_left hrem (by positivity)
    _ = ‖A‖ * C * E := by
      rw [norm_inv]
      calc
        _ = (‖A‖ * C * E) * (‖K‖⁻¹ * ‖K‖) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hK), mul_one]

namespace CompactSaddleFamily

namespace LocalSaddleData

noncomputable def index [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : ℕ := m + D.shift + S.firstIndex

noncomputable def center [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : ℂ := S.saddle (m + D.shift)

noncomputable def saddleKernel [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : ℂ :=
  normalizedKernel α₁ α₂ j (D.index m) ((largeScale (D.index m) : ℂ) * D.center m)

noncomputable def fullMoment [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m k : ℕ) : ℂ :=
  hankelIntegral (saddleContourRight (saddleScale α₁ α₂) j (D.center m))
    (saddleContourHeight (saddleScale α₁ α₂) j (D.center m))
    (fun s => s ^ k * normalizedKernel α₁ α₂ j (D.index m) ((largeScale (D.index m) : ℂ) * s))

noncomputable def gaussianNormalizer [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m : ℕ) : ℂ :=
  D.quadraticRoot m * ((largeScale (D.index m) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)

noncomputable def normalizedFullMoment [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (m k : ℕ) : ℂ :=
  D.gaussianNormalizer m * (branchOrientation j * D.saddleKernel m)⁻¹ * D.fullMoment m k

theorem index_tendsto [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : Tendsto D.index atTop atTop :=
  (tendsto_add_atTop_nat S.firstIndex).comp (tendsto_add_atTop_nat D.shift)

theorem eventually_saddleKernel_ne_zero [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∀ᶠ m : ℕ in atTop, D.saddleKernel m ≠ 0 := by
  filter_upwards [D.index_tendsto.eventually (eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j)] with m hm
  exact kernel_ne_zero j (D.index m) (hm.2 (S.saddle_mem_disk h₁ h₂ (m + D.shift)))

theorem fullMoment_leading_error [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (k : ℕ) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ᶠ m : ℕ in atTop,
      ‖D.fullMoment m k - branchOrientation j * D.saddleKernel m *
        D.localMoment (largeScale (D.index m)) k m‖ ≤
        C * ‖D.saddleKernel m‖ * Real.exp (-ε * largeScale (D.index m)) := by
  obtain ⟨ε, hε, C, hC, hb⟩ := uniform_full_window_remainder_bound h₁ h₂
    D.widths_pos.1 D.widths_pos.2 D.widths_lt.1 D.widths_lt.2 j S.errorConstant k
  refine ⟨ε, hε, C, hC, ?_⟩
  filter_upwards [D.index_tendsto.eventually hb, D.eventually_contourWindow_eq_phase h₁ h₂ k] with m hm hw
  have he := hm (D.center m) (S.saddle_mem_disk h₁ h₂ (m + D.shift)) (S.displacement (m + D.shift))
  dsimp only [center, index] at he
  rw [hw] at he
  exact he

theorem gaussianNormalizer_bound [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ B ≥ 0, ∀ m : ℕ, ‖D.gaussianNormalizer m‖ ≤ B * largeScale (D.index m) ^ (1 / 2 : ℝ) := by
  obtain ⟨B, hB, hb⟩ := D.uniform_quadraticRoot_bounds h₁ h₂
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨B / Real.Gamma (1 / 2 : ℝ), by positivity, fun m => ?_⟩
  have hscale : 0 ≤ largeScale (D.index m) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp : 0 ≤ largeScale (D.index m) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hscale _
  rw [gaussianNormalizer, norm_mul, Complex.norm_of_nonneg (div_nonneg hp hG.le)]
  calc
    _ ≤ B * (largeScale (D.index m) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (hb m).1 (div_nonneg hp hG.le)
    _ = _ := by ring

theorem normalizedFullMoment_tendsto [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (k : ℕ) :
    Tendsto (fun m : ℕ => D.normalizedFullMoment m k) atTop
      (𝓝 (((saddleScale α₁ α₂ : ℂ) * rho j) ^ k)) := by
  obtain ⟨ε, hε, C, hC, hrem⟩ := D.fullMoment_leading_error h₁ h₂ k
  obtain ⟨B, hB, hN⟩ := D.gaussianNormalizer_bound h₁ h₂
  have hbound : ∀ᶠ m : ℕ in atTop,
      ‖D.normalizedFullMoment m k - D.normalizedLocalMoment (largeScale (D.index m)) k m‖ ≤
        (B * C) * largeScale (D.index m) ^ (1 / 2 : ℝ) * Real.exp (-ε * largeScale (D.index m)) := by
    filter_upwards [hrem, D.eventually_saddleKernel_ne_zero h₁ h₂] with m hm hk
    have hn := norm_normalized_remainder_le
      (A := D.gaussianNormalizer m) (mul_ne_zero (branchOrientation_ne_zero j) hk)
      (by simpa only [norm_mul, norm_branchOrientation, one_mul] using hm)
    calc
      _ ≤ ‖D.gaussianNormalizer m‖ * C * Real.exp (-ε * largeScale (D.index m)) := hn
      _ ≤ (B * largeScale (D.index m) ^ (1 / 2 : ℝ)) * C *
          Real.exp (-ε * largeScale (D.index m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN m) hC) (Real.exp_pos _).le
      _ = _ := by ring
  have he : Tendsto (fun m : ℕ => D.normalizedFullMoment m k -
      D.normalizedLocalMoment (largeScale (D.index m)) k m) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound (by
      simpa only [Function.comp_def, mul_zero, mul_assoc] using
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) ε hε).comp
          (largeScale_tendsto.comp D.index_tendsto)).const_mul (B * C))
  simpa only [sub_add_cancel, zero_add, index] using
    he.add (D.normalizedLocalMoment_tendsto h₁ h₂ k)

end LocalSaddleData

end CompactSaddleFamily

end ThisWork.Analytic
