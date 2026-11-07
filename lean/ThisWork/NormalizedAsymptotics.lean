module

public import ThisWork.Argument
public import ThisWork.Definitions
public import ThisWork.IntegralNormBounds
public import ThisWork.KernelNorm

/-! The full norm estimate and linear independence asserted in Lemma 8. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology OnePoint

theorem log_difference_of_polynomial_bounds {x K A B : ℝ} {n : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hK : 0 < K) (hn : 1 ≤ n)
    (hl : K ≤ A * x) (hu : x ≤ B * (n : ℝ) ^ 3 * K) :
    0 < x ∧ |Real.log x - Real.log K| ≤
      (|Real.log A| + |Real.log B| + 9) * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hx : 0 < x := by
    by_contra! hx
    have hh := mul_nonpos_of_nonneg_of_nonpos hA.le hx
    linarith
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hll := Real.log_le_log hK hl
  rw [Real.log_mul hA.ne' hx.ne'] at hll
  have hlu := Real.log_le_log hx hu
  rw [Real.log_mul (mul_ne_zero hB.ne' (pow_ne_zero 3 hn0.ne')) hK.ne',
    Real.log_mul hB.ne' (pow_ne_zero 3 hn0.ne'), Real.log_pow] at hlu
  simp only [Nat.cast_ofNat] at hlu
  have hlog : Real.log (n : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 3)
    nlinarith
  have hp : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hconst : |Real.log A| + |Real.log B| ≤
      (|Real.log A| + |Real.log B|) * (n : ℝ) ^ (1 / 3 : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨hx, abs_le.mpr ⟨?_, ?_⟩⟩
  · nlinarith [le_abs_self (Real.log A), abs_nonneg (Real.log A), abs_nonneg (Real.log B)]
  · nlinarith [le_abs_self (Real.log B), abs_nonneg (Real.log A), abs_nonneg (Real.log B)]

namespace CompactSaddleFamily.LocalSaddleData

theorem eventually_rawCenter_displacement [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∀ᶠ n : ℕ in atTop, ‖D.rawCenter n - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤
      S.errorConstant * smallParameter n := by
  filter_upwards [eventually_ge_atTop D.offset] with n hn
  change D.shift + S.firstIndex ≤ n at hn
  have he : n - D.offset + D.shift + S.firstIndex = n := by dsimp only [offset]; omega
  simpa only [rawCenter, center, he] using S.displacement (n - D.offset + D.shift)

theorem rawKernel_log_norm_estimate [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖D.rawKernel n‖ - Real.log (gammaScale α₁ α₂ n) +
        3 * saddleScale α₁ α₂ * (rho j).re * largeScale n| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_kernel_near_saddle h₁ h₂ j S.errorConstant_nonneg
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, D.eventually_rawCenter_displacement] with n hn hd
  exact hn (D.rawCenter n) (D.rawCenter_mem_disk h₁ h₂ n) hd

/-- The Gaussian amplitude has the saddle exponential scale, with polynomial losses absorbed. -/
theorem gaussianAmplitude_log_norm_estimate [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖D.gaussianAmplitude n‖ - Real.log (gammaScale α₁ α₂ n) +
        3 * saddleScale α₁ α₂ * (rho j).re * largeScale n| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨A, hA, B, hB, hb⟩ := D.gaussianAmplitude_kernel_bounds h₁ h₂
  obtain ⟨C, hC, hk⟩ := D.rawKernel_log_norm_estimate h₁ h₂
  refine ⟨C + (|Real.log A| + |Real.log B| + 9), by positivity, ?_⟩
  filter_upwards [hb, hk, D.eventually_rawKernel_ne_zero h₁ h₂, eventually_ge_atTop (1 : ℕ)]
    with n hn hkernel hK hn1
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by exact_mod_cast hn1 : (1 : ℝ) ≤ n)
      (show 1 ≤ 3 by decide)
  have hu : ‖D.gaussianAmplitude n‖ ≤ B * (n : ℝ) ^ 3 * ‖D.rawKernel n‖ := by
    calc
      _ ≤ B * (n : ℝ) * ‖D.rawKernel n‖ := hn.2
      _ ≤ _ := by gcongr
  have hlog := (log_difference_of_polynomial_bounds hA hB (norm_pos_iff.mpr hK) hn1 hn.1 hu).2
  have he : Real.log ‖D.gaussianAmplitude n‖ - Real.log (gammaScale α₁ α₂ n) +
      3 * saddleScale α₁ α₂ * (rho j).re * largeScale n =
      (Real.log ‖D.gaussianAmplitude n‖ - Real.log ‖D.rawKernel n‖) +
      (Real.log ‖D.rawKernel n‖ - Real.log (gammaScale α₁ α₂ n) +
        3 * saddleScale α₁ α₂ * (rho j).re * largeScale n) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hlog hkernel).trans_eq (by ring))

theorem vector_log_norm_estimate [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      0 < ‖normalizedBranchIntegral α₁ α₂ j n‖ ∧
      |Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖ - Real.log (gammaScale α₁ α₂ n) +
        3 * saddleScale α₁ α₂ * (rho j).re * largeScale n| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨C, hC, hamp⟩ := D.gaussianAmplitude_log_norm_estimate h₁ h₂
  refine ⟨C + 7, by positivity, ?_⟩
  filter_upwards [hamp, D.eventually_vector_log_norm_shape h₁ h₂, eventually_ge_atTop (1 : ℕ)]
    with n ha hv hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hlog : Real.log (n : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 3)
    nlinarith
  refine ⟨hv.1, ?_⟩
  have he : Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖ - Real.log (gammaScale α₁ α₂ n) +
      3 * saddleScale α₁ α₂ * (rho j).re * largeScale n =
      (Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖ - Real.log ‖D.gaussianAmplitude n‖ - 2 * Real.log (n : ℝ)) +
      (Real.log ‖D.gaussianAmplitude n‖ - Real.log (gammaScale α₁ α₂ n) +
        3 * saddleScale α₁ α₂ * (rho j).re * largeScale n) + 2 * Real.log (n : ℝ) := by ring
  rw [he]
  calc
    _ ≤ |Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖ - Real.log ‖D.gaussianAmplitude n‖ - 2 * Real.log (n : ℝ)| +
        |Real.log ‖D.gaussianAmplitude n‖ - Real.log (gammaScale α₁ α₂ n) +
          3 * saddleScale α₁ α₂ * (rho j).re * largeScale n| + |2 * Real.log (n : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (Real.log_nonneg hn1)]
      nlinarith [hv.2, ha]

theorem norm_exp_estimate [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
      ‖normalizedBranchIntegral α₁ α₂ j n‖ = gammaScale α₁ α₂ n *
        Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * largeScale n + E) := by
  obtain ⟨C, hC, hb⟩ := D.vector_log_norm_estimate h₁ h₂
  refine ⟨C, hC, hb.mono (fun n hn => ?_)⟩
  let E := Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖ - Real.log (gammaScale α₁ α₂ n) +
    3 * saddleScale α₁ α₂ * (rho j).re * largeScale n
  refine ⟨E, hn.2, ?_⟩
  calc
    _ = Real.exp (Real.log ‖normalizedBranchIntegral α₁ α₂ j n‖) := (Real.exp_log hn.1).symm
    _ = Real.exp (Real.log (gammaScale α₁ α₂ n)) *
        Real.exp (-3 * saddleScale α₁ α₂ * (rho j).re * largeScale n + E) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [E]
      ring
    _ = _ := by rw [Real.exp_log (gammaScale_pos h₁ h₂ n)]

end CompactSaddleFamily.LocalSaddleData

theorem lemma8_normEstimate [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) :
    Lemma8NormEstimate α₁ α₂ := by
  intro j
  obtain ⟨S⟩ := exists_compactSaddleFamily h₁ h₂ j
  obtain ⟨D⟩ := S.exists_localSaddleData h₁ h₂
  obtain ⟨C, hC, hb⟩ := D.norm_exp_estimate h₁ h₂
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  exact ⟨C, hC, N, fun n hn => by simpa only [largeScale] using hN n hn⟩

/-- Lemma 8 of this work: both the norm estimate and independence of the
three concrete vector-valued integral sequences. -/
theorem lemma8 [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) : Lemma8 α₁ α₂ :=
  ⟨lemma8_normEstimate h₁ h₂, branchIntegral_linearIndependent h₁ h₂⟩

end ThisWork.Analytic
