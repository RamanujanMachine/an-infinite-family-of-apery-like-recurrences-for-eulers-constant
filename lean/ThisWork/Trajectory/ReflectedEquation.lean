module
public import ThisWork.Trajectory.ReflectionApproximation
public import ThisWork.Trajectory.SqrtSaddleDisk
/-! The reflected growing saddle, in positive coordinates `x = -sqrt(n)*s`. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

noncomputable def reflectedEquation (d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  -Complex.digamma ((d : ℂ) * n - (sqrtScale n : ℂ) * s) +
    Complex.digamma ((A₁ : ℂ) * n + (sqrtScale n : ℂ) * s + 1) +
    Complex.digamma ((A₂ : ℂ) * n + (sqrtScale n : ℂ) * s + 1) -
    2 * Complex.digamma (1 + (sqrtScale n : ℂ) * s) + (Real.log z : ℂ)

theorem norm_reflectedEquation_add_limit_le {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    {n : ℕ} (hn : 0 < n) {M : ℝ} {s : ℂ} (hs : ‖s‖ ≤ M) (hslit : s ∈ Complex.slitPlane)
    (hD : 4 ≤ (d : ℝ) * n) (hA₁ : 4 ≤ A₁ * n) (hA₂ : 4 ≤ A₂ * n)
    (hMD : sqrtScale n * M ≤ ((d : ℝ) * n) / 4)
    (hM₁ : sqrtScale n * M ≤ (A₁ * n) / 4)
    (hM₂ : sqrtScale n * M ≤ (A₂ * n) / 4) :
    ‖reflectedEquation d A₁ A₂ z n s + sqrtEquation (doubleSaddleScale d A₁ A₂ z) s‖ ≤
      2 * ‖Complex.digamma ((sqrtScale n : ℂ) * s) - Complex.log ((sqrtScale n : ℂ) * s)‖ +
      (4 / ((d : ℝ) * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / ((d : ℝ) * n)) +
        2 / ((d : ℝ) * n)) +
      (4 / (A₁ * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / (A₁ * n))) +
      (4 / (A₂ * n) + (3 / 2 : ℝ) * ((1 + sqrtScale n * M) / (A₂ * n))) +
      2 * ‖((sqrtScale n : ℂ) * s)⁻¹‖ := by
  let R := sqrtScale n
  let L₀ := Complex.digamma ((R : ℂ) * s) - Complex.log ((R : ℂ) * s)
  let LD := Complex.digamma ((d : ℂ) * n - (R : ℂ) * s) - Complex.log (((d : ℝ) * n : ℝ) : ℂ)
  let L₁ := Complex.digamma ((A₁ : ℂ) * n + (R : ℂ) * s + 1) - Complex.log ((A₁ * n : ℝ) : ℂ)
  let L₂ := Complex.digamma ((A₂ : ℂ) * n + (R : ℂ) * s + 1) - Complex.log ((A₂ * n : ℝ) : ℂ)
  have hR : 0 < R := sqrtScale_pos hn
  have hs0 := Complex.slitPlane_ne_zero hslit
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlogR : (2 : ℂ) * (Real.log R : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact_mod_cast log_sqrtScale hn
  have hlog (a : ℝ) (ha : 0 < a) :
      Complex.log ((a * n : ℝ) : ℂ) = (Real.log a : ℂ) + (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (mul_pos ha hnR).le,
      Real.log_mul ha.ne' hnR.ne', Complex.ofReal_add]
  have hψ := Complex.digamma_apply_add_one ((R : ℂ) * s)
    (not_neg_nat_of_mem_slitPlane ((div_pos_real_mem_slitPlane_iff hR _).mp (by
      simpa only [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')] using hslit)))
  have he : reflectedEquation d A₁ A₂ z n s + sqrtEquation (doubleSaddleScale d A₁ A₂ z) s =
      -2 * L₀ - LD + L₁ + L₂ - 2 * ((R : ℂ) * s)⁻¹ := by
    have hlim := limitingSqrtEquation_eq_logs hd h₁ h₂ hz .three hs0
    simp only [limitingSqrtEquation, twist_three, add_zero] at hlim
    rw [hlim]
    dsimp only [reflectedEquation, L₀, LD, L₁, L₂, R] at hψ ⊢
    rw [show 1 + (sqrtScale n : ℂ) * s = (sqrtScale n : ℂ) * s + 1 by ring, hψ,
      Complex.log_ofReal_mul hR hs0, hlog _ (Nat.cast_pos.mpr hd), hlog A₁ h₁, hlog A₂ h₂]
    linear_combination -hlogR
  have hbD : ‖LD‖ ≤ 4 / ((d : ℝ) * n) + (3 / 2 : ℝ) * ((1 + R * M) / ((d : ℝ) * n)) +
      2 / ((d : ℝ) * n) := by
    simpa only [LD, Complex.ofReal_mul, Complex.ofReal_natCast, mul_neg, ← sub_eq_add_neg] using
      norm_digamma_affine_add_sub_log_le hD hR.le hMD (s := -s) (by simpa only [norm_neg] using hs)
  have hb₁ : ‖L₁‖ ≤ 4 / (A₁ * n) + (3 / 2 : ℝ) * ((1 + R * M) / (A₁ * n)) := by
    simpa only [L₁, Complex.ofReal_mul, Complex.ofReal_natCast, mul_neg, sub_neg_eq_add] using
      norm_digamma_affine_sub_log_le hA₁ hR.le hM₁ (s := -s) (by simpa only [norm_neg] using hs)
  have hb₂ : ‖L₂‖ ≤ 4 / (A₂ * n) + (3 / 2 : ℝ) * ((1 + R * M) / (A₂ * n)) := by
    simpa only [L₂, Complex.ofReal_mul, Complex.ofReal_natCast, mul_neg, sub_neg_eq_add] using
      norm_digamma_affine_sub_log_le hA₂ hR.le hM₂ (s := -s) (by simpa only [norm_neg] using hs)
  rw [he]
  calc
    _ ≤ ‖-2 * L₀ - LD + L₁ + L₂‖ + ‖2 * ((R : ℂ) * s)⁻¹‖ := norm_sub_le _ _
    _ ≤ ((‖-2 * L₀‖ + ‖LD‖) + ‖L₁‖) + ‖L₂‖ + ‖2 * ((R : ℂ) * s)⁻¹‖ :=
      add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)) le_rfl
    _ ≤ _ := by
      simpa only [norm_mul, norm_neg, Complex.norm_ofNat, L₀, R] using
        add_le_add (add_le_add (add_le_add (add_le_add le_rfl hbD) hb₁) hb₂) le_rfl

theorem uniform_reflectedEquation_right {d : ℕ} {A₁ A₂ z η : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hη : 0 < η) {K : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ s ∈ K, ‖s‖ ≤ M) (hregion : ∀ s ∈ K, η ≤ s.re) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s ∈ K,
      ‖reflectedEquation d A₁ A₂ z n s + sqrtEquation (doubleSaddleScale d A₁ A₂ z) s‖ ≤
        C / sqrtScale n := by
  let L := fun a : ℝ => (11 + 3 * M) / (2 * a)
  refine ⟨6 / η + L d + 2 / d + L A₁ + L A₂, by dsimp [L]; positivity, ?_⟩
  filter_upwards [sqrtScale_tendsto.eventually (Analytic.uniform_scaled_digamma_right hη),
    eventually_right_factor_conditions (Nat.cast_pos.mpr hd) M,
    eventually_right_factor_conditions h₁ M, eventually_right_factor_conditions h₂ M,
    eventually_ge_atTop (1 : ℕ)] with n hψ hD hA₁ hA₂ hn
  intro s hs
  have hb := norm_reflectedEquation_add_limit_le hd h₁ h₂ hz (by omega : 0 < n)
    (hK s hs) (Complex.mem_slitPlane_iff.mpr (Or.inl (hη.trans_le (hregion s hs)))) hD.1 hA₁.1 hA₂.1 hD.2 hA₁.2 hA₂.2
  have hInv : 2 / ((d : ℝ) * n) ≤ (2 / d) * (1 / sqrtScale n) := by
    calc
      _ = (2 / d) * (1 / (n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_nat_le_inv_sqrtScale hn) (by positivity)
  have hInvS : ‖((sqrtScale n : ℂ) * s)⁻¹‖ ≤ (1 / η) * (1 / sqrtScale n) := by
    rw [norm_inv, norm_mul, Complex.norm_of_nonneg (sqrtScale_pos (by omega)).le]
    calc
      _ ≤ (sqrtScale n * η)⁻¹ := inv_anti₀ (mul_pos hψ.1 hη)
        (mul_le_mul_of_nonneg_left ((hregion s hs).trans (Complex.re_le_norm s)) (sqrtScale_pos (by omega)).le)
      _ = _ := by ring
  have hpartial := (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (hψ.2 s (hregion s hs)) (by norm_num : (0 : ℝ) ≤ 2))
      (add_le_add (affineError_le_inv_sqrtScale (Nat.cast_pos.mpr hd) hn M) hInv))
    (affineError_le_inv_sqrtScale h₁ hn M))
    (affineError_le_inv_sqrtScale h₂ hn M))
  have hbound := hb.trans (add_le_add hpartial (mul_le_mul_of_nonneg_left hInvS (by norm_num : (0 : ℝ) ≤ 2)))
  exact hbound.trans_eq (by dsimp only [L]; ring)

end ThisWork.Trajectory
