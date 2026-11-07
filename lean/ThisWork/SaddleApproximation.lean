module

public import ThisWork.Argument
public import ThisWork.Parameters
public import ThisWork.AffineDigamma

/-! Quantitative comparison of the exact and limiting saddle equations. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem norm_exactSaddleEquation_sub_limit_le [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {n : ℕ} (hn : 0 < n) {M : ℝ} {s : ℂ} (hs : ‖s‖ ≤ M) (hs0 : s ≠ 0)
    (hA₁ : 4 ≤ α₁ * n) (hA₂ : 4 ≤ α₂ * n)
    (hM₁ : largeScale n * M ≤ (α₁ * n) / 4) (hM₂ : largeScale n * M ≤ (α₂ * n) / 4) :
    ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤
      3 * ‖Complex.digamma ((largeScale n : ℂ) * s) - Complex.log ((largeScale n : ℂ) * s)‖ +
      (4 / (α₁ * n) + (3 / 2 : ℝ) * ((1 + largeScale n * M) / (α₁ * n))) +
      (4 / (α₂ * n) + (3 / 2 : ℝ) * ((1 + largeScale n * M) / (α₂ * n))) := by
  let R := largeScale n
  let L₀ := Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)
  let L₁ := Complex.digamma ((α₁ : ℂ) * n - (R : ℂ) * s + 1) - Complex.log ((α₁ * n : ℝ) : ℂ)
  let L₂ := Complex.digamma ((α₂ : ℂ) * n - (R : ℂ) * s + 1) - Complex.log ((α₂ * n : ℝ) : ℂ)
  have hR : 0 < R := largeScale_pos hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlogR : (3 : ℂ) * (Real.log R : ℂ) = 2 * (Real.log (n : ℝ) : ℂ) := by
    exact_mod_cast log_largeScale hn
  have hlog₁ : Complex.log ((α₁ * n : ℝ) : ℂ) = (Real.log α₁ : ℂ) + (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos h₁ hnR).le, Real.log_mul h₁.ne' hnR.ne', Complex.ofReal_add]
  have hlog₂ : Complex.log ((α₂ * n : ℝ) : ℂ) = (Real.log α₂ : ℂ) + (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos h₂ hnR).le, Real.log_mul h₂.ne' hnR.ne', Complex.ofReal_add]
  have he : exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s =
      3 * L₀ - L₁ - L₂ := by
    rw [limitingEquation_eq_logs h₁ h₂ j hs0]
    dsimp [exactSaddleEquation, kernelLogDerivative, L₀, L₁, L₂]
    rw [Complex.log_ofReal_mul hR hs0, hlog₁, hlog₂]
    linear_combination hlogR
  have hb₁ : ‖L₁‖ ≤ 4 / (α₁ * n) + (3 / 2 : ℝ) * ((1 + R * M) / (α₁ * n)) := by
    simpa only [L₁, Complex.ofReal_mul, Complex.ofReal_natCast] using
      norm_digamma_affine_sub_log_le hA₁ hR.le hM₁ hs
  have hb₂ : ‖L₂‖ ≤ 4 / (α₂ * n) + (3 / 2 : ℝ) * ((1 + R * M) / (α₂ * n)) := by
    simpa only [L₂, Complex.ofReal_mul, Complex.ofReal_natCast] using
      norm_digamma_affine_sub_log_le hA₂ hR.le hM₂ hs
  rw [he]
  have htri := (norm_sub_le (3 * L₀ - L₁) L₂).trans
    (add_le_add (norm_sub_le (3 * L₀) L₁) le_rfl)
  have htri' := htri.trans (add_le_add (add_le_add (le_refl ‖3 * L₀‖) hb₁) hb₂)
  simpa [norm_mul, L₀, R] using htri'

theorem eventually_right_factor_conditions {α : ℝ} (hα : 0 < α) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 4 ≤ α * n ∧ largeScale n * M ≤ (α * n) / 4 := by
  have hratio : Tendsto (fun n : ℕ => (largeScale n / (n : ℝ)) * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using largeScale_div_nat_tendsto.mul_const M
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (4 / α)), hratio.eventually (gt_mem_nhds (show (0 : ℝ) < α / 4 from div_pos hα (by norm_num))),
    eventually_gt_atTop (0 : ℕ)] with n hn hsmall hn0
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hα).mp hn, ?_⟩
  rw [div_mul_eq_mul_div] at hsmall
  exact ((div_lt_iff₀ (Nat.cast_pos.mpr hn0)).mp hsmall).le.trans_eq (by ring)

theorem affineError_le_smallParameter {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) (M : ℝ) :
    4 / (α * n) + (3 / 2 : ℝ) * ((1 + largeScale n * M) / (α * n)) ≤
      ((11 + 3 * M) / (2 * α)) * smallParameter n := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 4 / (α * n) + (3 / 2 : ℝ) * ((1 + largeScale n * M) / (α * n)) =
      (11 / (2 * α)) * (1 / (n : ℝ)) + ((3 * M) / (2 * α)) * (largeScale n / (n : ℝ)) := by
    field_simp
    ring
  rw [he, largeScale_div_nat hn0]
  have h := add_le_add (mul_le_mul_of_nonneg_left (inv_nat_le_smallParameter hn)
    (show 0 ≤ 11 / (2 * α) by positivity)) (le_refl (((3 * M) / (2 * α)) * smallParameter n))
  exact h.trans_eq (by ring)

/-- Uniform `O(n^(-1/3))` control of the exact saddle equation follows from
the proved scaled digamma bounds and a bounded source region. -/
theorem uniform_saddleApprox_from_digamma [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {K : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ s ∈ K, ‖s‖ ≤ M) (hne : ∀ s ∈ K, s ≠ 0)
    (hψ : ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      ‖Complex.digamma ((largeScale n : ℂ) * s) - Complex.log ((largeScale n : ℂ) * s)‖ ≤ C / largeScale n) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤ C * smallParameter n := by
  obtain ⟨C₀, hC₀, hψ⟩ := hψ
  refine ⟨3 * C₀ + (11 + 3 * M) / (2 * α₁) + (11 + 3 * M) / (2 * α₂), by positivity, ?_⟩
  filter_upwards [hψ, eventually_right_factor_conditions h₁ M,
    eventually_right_factor_conditions h₂ M, eventually_ge_atTop (1 : ℕ)] with n hψ hn₁ hn₂ hn
  intro s hs
  have hp := norm_exactSaddleEquation_sub_limit_le h₁ h₂ j (lt_of_lt_of_le zero_lt_one hn)
    (hK s hs) (hne s hs) hn₁.1 hn₂.1 hn₁.2 hn₂.2
  have hfirst : 3 * ‖Complex.digamma ((largeScale n : ℂ) * s) - Complex.log ((largeScale n : ℂ) * s)‖ ≤
      (3 * C₀) * smallParameter n := by
    calc
      _ ≤ 3 * (C₀ / largeScale n) := mul_le_mul_of_nonneg_left (hψ s hs) (by norm_num)
      _ = (3 * C₀) * (1 / largeScale n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_largeScale_le_smallParameter hn) (by positivity)
  have hb := hp.trans (add_le_add (add_le_add hfirst (affineError_le_smallParameter h₁ hn M))
    (affineError_le_smallParameter h₂ hn M))
  exact hb.trans_eq (by ring)

theorem uniform_exactSaddleEquation_right [PositiveArgument] {α₁ α₂ κ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (hκ : 0 < κ) (j : Branch) {K : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ s ∈ K, ‖s‖ ≤ M) (hregion : ∀ s ∈ K, κ ≤ s.re) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤ C * smallParameter n := by
  apply uniform_saddleApprox_from_digamma h₁ h₂ j hM hK
    (fun s hs he => by have h := hregion s hs; rw [he, Complex.zero_re] at h; linarith)
  refine ⟨2 / κ, by positivity, ?_⟩
  filter_upwards [largeScale_tendsto.eventually (uniform_scaled_digamma_right hκ)] with n hn s hs
  exact hn.2 s (hregion s hs)

theorem uniform_exactSaddleEquation_left [PositiveArgument] {α₁ α₂ κ η : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (hκ : 0 < κ) (hη : 0 < η) (j : Branch) {K : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ s ∈ K, ‖s‖ ≤ M) (hregion : ∀ s ∈ K, s.re ≤ -κ ∧ η ≤ |s.im|) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤ C * smallParameter n := by
  apply uniform_saddleApprox_from_digamma h₁ h₂ j hM hK
    (fun s hs he => by have h := (hregion s hs).1; rw [he, Complex.zero_re] at h; linarith)
  refine ⟨2 / κ + 4 * Real.pi, by positivity, ?_⟩
  filter_upwards [largeScale_tendsto.eventually (uniform_scaled_digamma_left hκ hη)] with n hn s hs
  exact hn.2 s (hregion s hs).1 (hregion s hs).2

end ThisWork.Analytic
