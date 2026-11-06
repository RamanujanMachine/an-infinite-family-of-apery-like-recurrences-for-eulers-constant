module

public import ThisWork.KernelNorm

/-! Gamma estimates for horizontal Mellin–Barnes tails. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem uniform_Gamma_bounded_shift {M : ℝ} (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ A : ℝ in atTop, 1 ≤ A ∧ ∀ s : ℂ, ‖s‖ ≤ M →
      |Real.log ‖Complex.Gamma ((A : ℂ) - s + 1)‖ -
        Real.log ‖Complex.Gamma ((A + 1 : ℝ) : ℂ)‖ + s.re * Real.log A| ≤ C / A := by
  let C := M * ((11 + 6 * M) / 2)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (8 * M)] with A hA hAM
  refine ⟨by linarith, fun s hs => ?_⟩
  have h := abs_log_norm_Gamma_affine_sub_le hA (R := 1) zero_lt_one hM (by nlinarith) hs
  simp only [Complex.ofReal_one, one_mul, mul_one] at h
  convert h using 1
  dsimp only [C]
  ring

theorem log_norm_Gamma_reflection {z : ℂ} (hre : z.re < 0) (him : z.im ≠ 0) :
    Real.log ‖Complex.Gamma z‖ = Real.log Real.pi - Real.log ‖z‖ -
      Real.log ‖Complex.sin ((Real.pi : ℂ) * z)‖ - Real.log ‖Complex.Gamma (-z)‖ := by
  have h := gammaNormError_reflection hre him
  dsimp only [gammaNormError] at h
  linarith [stirlingMain_reflection_re him]

theorem log_norm_Gamma_real_lower {a : ℝ} (ha : 2 ≤ a) :
    a * Real.log a - a - |gammaNormError 2| - 2 * Real.log a ≤
      Real.log ‖Complex.Gamma (a : ℂ)‖ := by
  have h := abs_gammaNormError_right (z := (a : ℂ)) (by simpa only [Complex.ofReal_re] using ha)
  have hmain : (stirlingMain (a : ℂ)).re = a * (Real.log a - 1) := by
    simp [stirlingMain, ← Complex.ofReal_log (show 0 ≤ a by linarith), Complex.mul_re]
  simp only [gammaNormError, hmain, Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, zero_div, add_zero] at h
  change |Real.log ‖Complex.Gamma (a : ℂ)‖ - a * (Real.log a - 1)| ≤ |gammaNormError 2| + 2 * Real.log a at h
  nlinarith [(abs_le.mp h).1]

theorem sine_tail_exp_bound {y : ℝ} (hy : 1 ≤ |y|) :
    Real.exp (-2 * Real.pi * |y|) ≤ 1 / 2 := by
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have harg : 1 ≤ 2 * Real.pi * |y| :=
    hπ.trans (le_mul_of_one_le_right (by positivity : 0 ≤ 2 * Real.pi) hy)
  have he : 2 ≤ Real.exp (2 * Real.pi * |y|) := by linarith [Real.add_one_le_exp (2 * Real.pi * |y|)]
  rw [show -2 * Real.pi * |y| = -(2 * Real.pi * |y|) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he

theorem uniform_log_norm_Gamma_shift {M : ℝ} (hM : 0 < M) :
    ∃ C ≥ 0, ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ ∀ d : ℂ, ‖d‖ ≤ M →
      |Real.log ‖Complex.Gamma ((T : ℂ) + d)‖ - Real.log ‖Complex.Gamma (T : ℂ)‖ -
        d.re * Real.log (T - 1)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_Gamma_bounded_shift hM
  have hT : Tendsto (fun T : ℝ => T - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  refine ⟨C, hC, ?_⟩
  filter_upwards [hT.eventually hb] with T hT
  refine ⟨by linarith [hT.1], fun d hd => ?_⟩
  have h := hT.2 (-d) (by simpa only [norm_neg] using hd)
  rw [show ((T - 1 : ℝ) : ℂ) - -d + 1 = (T : ℂ) + d by push_cast; ring, sub_add_cancel] at h
  simp only [Complex.neg_re, neg_mul, ← sub_eq_add_neg] at h
  exact h.trans ((div_le_iff₀ (by linarith [hT.1] : 0 < T - 1)).mpr
    (by nlinarith [hT.1]))

theorem eventually_log_tail_le (A B q : ℝ) :
    ∀ᶠ T : ℝ in atTop, 0 < T ∧ -T * Real.log T + T + A * Real.log T + B ≤ -q * T := by
  filter_upwards [eventually_ge_atTop (max 1 (2 * A)), eventually_ge_atTop B,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 0 (2 * (q + 2))))]
    with T hTA hB hlog
  have hT₁ := (le_max_left 1 (2 * A)).trans hTA
  have hT₂ := (le_max_right 1 (2 * A)).trans hTA
  have hlog₀ := (le_max_left 0 (2 * (q + 2))).trans hlog
  have hlog₁ := (le_max_right 0 (2 * (q + 2))).trans hlog
  exact ⟨by linarith, by nlinarith [mul_le_mul_of_nonneg_right hT₂ hlog₀,
    mul_le_mul_of_nonneg_right hlog₁ (show 0 ≤ T by linarith)]⟩

theorem uniform_log_norm_Gamma_strip_shift {D H : ℝ} (hD : 0 ≤ D) (hH : 0 < H) :
    ∃ C ≥ 0, ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ ∀ a : ℝ, 0 ≤ a → a ≤ D →
      ∀ y : ℝ, |y| ≤ H →
      |Real.log ‖Complex.Gamma ((T : ℂ) + (a : ℂ) + (y : ℂ) * Complex.I)‖ -
        Real.log ‖Complex.Gamma (T : ℂ)‖ - a * Real.log (T - 1)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_Gamma_shift (show 0 < D + H by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with T hT
  refine ⟨hT.1, fun a ha haD y hy => ?_⟩
  have hd : ‖(a : ℂ) + (y : ℂ) * Complex.I‖ ≤ D + H := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = a + |y| := by rw [Complex.norm_of_nonneg ha]; simp
      _ ≤ D + H := add_le_add haD hy
  simpa [add_assoc, Complex.mul_re] using hT.2 _ hd

end ThisWork
