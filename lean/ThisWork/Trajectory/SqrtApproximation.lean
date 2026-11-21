module

public import ThisWork.Trajectory.SqrtSaddleEquation

/-! Quantitative comparison of the actual double-minimum saddle equation
with its logarithmic limit, retaining an arbitrary positive argument. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

theorem norm_exactSqrtEquation_sub_limit_le {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (j : Branch) {n : ℕ} (hn : 0 < n) {M : ℝ} {s : ℂ} (hs : ‖s‖ ≤ M) (hs0 : s ≠ 0)
    (hD : 4 ≤ (d : ℝ) * n) (hA₁ : 4 ≤ A₁ * n) (hA₂ : 4 ≤ A₂ * n)
    (hMD : sqrtScale n * M ≤ ((d : ℝ) * n) / 4)
    (hM₁ : sqrtScale n * M ≤ (A₁ * n) / 4)
    (hM₂ : sqrtScale n * M ≤ (A₂ * n) / 4) :
    ‖exactSqrtEquation d A₁ A₂ z j n s - limitingSqrtEquation d A₁ A₂ z j s‖ ≤
      2 * ‖Complex.digamma ((sqrtScale n : ℂ) * s) - Complex.log ((sqrtScale n : ℂ) * s)‖ +
      (4 / ((d : ℝ) * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / ((d : ℝ) * n)) +
        2 / ((d : ℝ) * n)) +
      (4 / (A₁ * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / (A₁ * n))) +
      (4 / (A₂ * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / (A₂ * n))) := by
  let R := sqrtScale n
  let L₀ := Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)
  let LD := Complex.digamma ((d : ℂ) * n + (R : ℂ) * s) - Complex.log (((d : ℝ) * n : ℝ) : ℂ)
  let L₁ := Complex.digamma ((A₁ : ℂ) * n - (R : ℂ) * s + 1) - Complex.log ((A₁ * n : ℝ) : ℂ)
  let L₂ := Complex.digamma ((A₂ : ℂ) * n - (R : ℂ) * s + 1) - Complex.log ((A₂ * n : ℝ) : ℂ)
  have hR : 0 < R := sqrtScale_pos hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlogR : (2 : ℂ) * (Real.log R : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact_mod_cast log_sqrtScale hn
  have hlog (a : ℝ) (ha : 0 < a) :
      Complex.log ((a * n : ℝ) : ℂ) = (Real.log a : ℂ) + (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos ha hnR).le,
      Real.log_mul ha.ne' hnR.ne', Complex.ofReal_add]
  have he : exactSqrtEquation d A₁ A₂ z j n s - limitingSqrtEquation d A₁ A₂ z j s =
      2 * L₀ + LD - L₁ - L₂ := by
    rw [limitingSqrtEquation_eq_logs hd h₁ h₂ hz j hs0]
    dsimp [exactSqrtEquation, kernelLogDerivative, L₀, LD, L₁, L₂]
    rw [Complex.log_ofReal_mul hR hs0, hlog _ (Nat.cast_pos.mpr hd), hlog A₁ h₁, hlog A₂ h₂]
    linear_combination hlogR
  have hbD : ‖LD‖ ≤ 4 / ((d : ℝ) * n) + (3 / 2 : ℝ) * ((1 + R * M) / ((d : ℝ) * n)) +
      2 / ((d : ℝ) * n) := by
    simpa only [LD, Complex.ofReal_mul, Complex.ofReal_natCast] using
      norm_digamma_affine_add_sub_log_le hD hR.le hMD hs
  have hb₁ : ‖L₁‖ ≤ 4 / (A₁ * n) + (3 / 2 : ℝ) * ((1 + R * M) / (A₁ * n)) := by
    simpa only [L₁, Complex.ofReal_mul, Complex.ofReal_natCast] using
      Analytic.norm_digamma_affine_sub_log_le hA₁ hR.le hM₁ hs
  have hb₂ : ‖L₂‖ ≤ 4 / (A₂ * n) + (3 / 2 : ℝ) * ((1 + R * M) / (A₂ * n)) := by
    simpa only [L₂, Complex.ofReal_mul, Complex.ofReal_natCast] using
      Analytic.norm_digamma_affine_sub_log_le hA₂ hR.le hM₂ hs
  rw [he]
  calc
    _ ≤ ((‖2 * L₀‖ + ‖LD‖) + ‖L₁‖) + ‖L₂‖ :=
      (norm_sub_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by simpa only [norm_mul, Complex.norm_ofNat, L₀, R] using
      add_le_add (add_le_add (add_le_add le_rfl hbD) hb₁) hb₂

/-- Uniform `O(n^(-1/2))` control on bounded regions of the right half-plane. -/
theorem uniform_exactSqrtEquation_right {d : ℕ} {A₁ A₂ z η : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) (j : Branch) {K : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ s ∈ K, ‖s‖ ≤ M) (hregion : ∀ s ∈ K, η ≤ s.re) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      ‖exactSqrtEquation d A₁ A₂ z j n s - limitingSqrtEquation d A₁ A₂ z j s‖ ≤
        C / sqrtScale n := by
  let L := fun a : ℝ => (11 + 3 * M) / (2 * a)
  refine ⟨4 / η + L d + 2 / d + L A₁ + L A₂, by dsimp [L]; positivity, ?_⟩
  filter_upwards [sqrtScale_tendsto.eventually (Analytic.uniform_scaled_digamma_right hη),
    eventually_right_factor_conditions (Nat.cast_pos.mpr hd) M,
    eventually_right_factor_conditions h₁ M, eventually_right_factor_conditions h₂ M,
    eventually_ge_atTop (1 : ℕ)] with n hψ hD hA₁ hA₂ hn
  intro s hs
  have hs0 : s ≠ 0 := by
    intro he
    have h := hregion s hs
    simp only [he, Complex.zero_re] at h
    linarith
  have hb := norm_exactSqrtEquation_sub_limit_le hd h₁ h₂ hz j (by omega : 0 < n)
    (hK s hs) hs0 hD.1 hA₁.1 hA₂.1 hD.2 hA₁.2 hA₂.2
  have hInv : 2 / ((d : ℝ) * n) ≤ (2 / d) * (1 / sqrtScale n) := by
    calc
      _ = (2 / d) * (1 / (n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_nat_le_inv_sqrtScale hn) (by positivity)
  have hbound := hb.trans (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (hψ.2 s (hregion s hs)) (by norm_num))
      (add_le_add (affineError_le_inv_sqrtScale (Nat.cast_pos.mpr hd) hn M) hInv))
    (affineError_le_inv_sqrtScale h₁ hn M))
    (affineError_le_inv_sqrtScale h₂ hn M))
  exact hbound.trans_eq (by dsimp only [L]; ring)

end ThisWork.Trajectory
