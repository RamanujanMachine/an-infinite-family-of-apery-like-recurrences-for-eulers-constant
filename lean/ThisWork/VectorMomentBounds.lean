module

public import ThisWork.HankelMoments

/-! Elementary norm bounds for the three-component moment coordinate change. -/

@[expose] public section

namespace ThisWork

open Set Filter
open scoped Topology

theorem momentTransform_recover_first (n : ℕ) {R : ℝ} (hR : R ≠ 0) (v : Fin 3 → ℂ) :
    (n : ℂ) * momentTransform n R v 0 - (R : ℂ) * momentTransform n R v 1 = v 1 := by
  simp [momentTransform]
  field_simp [Complex.ofReal_ne_zero.mpr hR]
  ring

theorem momentTransform_recover_second (n : ℕ) {R : ℝ} (hR : R ≠ 0) (v : Fin 3 → ℂ) :
    (n : ℂ) ^ 2 * momentTransform n R v 0 -
      2 * (n : ℂ) * (R : ℂ) * momentTransform n R v 1 +
      (R : ℂ) ^ 2 * momentTransform n R v 2 = v 2 := by
  simp [momentTransform]
  field_simp [Complex.ofReal_ne_zero.mpr hR]
  ring

noncomputable def inverseMomentTransform (n : ℕ) (R : ℝ) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun w := ![w 0, (n : ℂ) * w 0 - (R : ℂ) * w 1,
    (n : ℂ) ^ 2 * w 0 - 2 * (n : ℂ) * (R : ℂ) * w 1 + (R : ℂ) ^ 2 * w 2]
  map_add' := by intro v w; ext k; fin_cases k <;> simp <;> ring
  map_smul' := by intro c v; ext k; fin_cases k <;> simp [smul_eq_mul] <;> ring

theorem inverseMomentTransform_left_inverse (n : ℕ) {R : ℝ} (hR : R ≠ 0) (v : Fin 3 → ℂ) :
    inverseMomentTransform n R (momentTransform n R v) = v := by
  ext k
  fin_cases k
  · simp [inverseMomentTransform, momentTransform]
  · simpa [inverseMomentTransform] using momentTransform_recover_first n hR v
  · simpa [inverseMomentTransform] using momentTransform_recover_second n hR v

theorem norm_inverseMomentTransform_le {n : ℕ} {R M : ℝ}
    (hn : 1 ≤ n) (hR : 0 ≤ R) (hRn : R ≤ n) (hM : 0 ≤ M) (w : Fin 3 → ℂ)
    (hw : ∀ k, ‖w k‖ ≤ M) :
    ‖inverseMomentTransform n R w‖ ≤ 4 * (n : ℝ) ^ 2 * M := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (Nat.cast_nonneg (α := ℝ) n)]
  have hnR : (n : ℝ) * R ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hRn (Nat.cast_nonneg (α := ℝ) n)]
  have hR2 : R ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hR hRn 2
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  fin_cases k
  · change ‖w 0‖ ≤ _
    exact (hw 0).trans (by nlinarith [mul_le_mul_of_nonneg_right hnsq hM, mul_le_mul_of_nonneg_right hn1 hM])
  · change ‖(n : ℂ) * w 0 - (R : ℂ) * w 1‖ ≤ _
    calc
      _ ≤ ‖(n : ℂ) * w 0‖ + ‖(R : ℂ) * w 1‖ := norm_sub_le _ _
      _ = (n : ℝ) * ‖w 0‖ + R * ‖w 1‖ := by rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_of_nonneg hR]
      _ ≤ (n : ℝ) * M + R * M := add_le_add
        (mul_le_mul_of_nonneg_left (hw 0) (Nat.cast_nonneg n)) (mul_le_mul_of_nonneg_left (hw 1) hR)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hnsq hM, mul_le_mul_of_nonneg_right hRn hM]
  · change ‖(n : ℂ) ^ 2 * w 0 - 2 * (n : ℂ) * (R : ℂ) * w 1 + (R : ℂ) ^ 2 * w 2‖ ≤ _
    calc
      _ ≤ ‖(n : ℂ) ^ 2 * w 0 - 2 * (n : ℂ) * (R : ℂ) * w 1‖ + ‖(R : ℂ) ^ 2 * w 2‖ :=
        norm_add_le _ _
      _ ≤ (‖(n : ℂ) ^ 2 * w 0‖ + ‖2 * (n : ℂ) * (R : ℂ) * w 1‖) + ‖(R : ℂ) ^ 2 * w 2‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ = (n : ℝ) ^ 2 * ‖w 0‖ + 2 * (n : ℝ) * R * ‖w 1‖ + R ^ 2 * ‖w 2‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_of_nonneg hR, RCLike.norm_two]
      _ ≤ (n : ℝ) ^ 2 * M + 2 * (n : ℝ) * R * M + R ^ 2 * M := by
        gcongr <;> exact hw _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hnR hM, mul_le_mul_of_nonneg_right hR2 hM]

theorem norm_vector_le_of_normalized_moments {n : ℕ} {R M : ℝ} {a : ℂ}
    (hn : 1 ≤ n) (hR : 0 < R) (hRn : R ≤ n) (hM : 0 ≤ M) (ha : a ≠ 0)
    (v : Fin 3 → ℂ) (hv : ∀ k, ‖a * momentTransform n R v k‖ ≤ M) :
    ‖v‖ ≤ 4 * (n : ℝ) ^ 2 * M * ‖a⁻¹‖ := by
  let g : Fin 3 → ℂ := fun k => a * momentTransform n R v k
  have he : v = a⁻¹ • inverseMomentTransform n R g := by
    symm
    change a⁻¹ • inverseMomentTransform n R (a • momentTransform n R v) = v
    rw [LinearMap.map_smul, inverseMomentTransform_left_inverse n hR.ne',
      smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [he, norm_smul]
  calc
    _ ≤ ‖a⁻¹‖ * (4 * (n : ℝ) ^ 2 * M) :=
      mul_le_mul_of_nonneg_left (norm_inverseMomentTransform_le hn hR.le hRn hM g hv) (norm_nonneg _)
    _ = _ := by ring

theorem norm_first_normalized_moment_le (n : ℕ) (R : ℝ) (a : ℂ) (v : Fin 3 → ℂ) :
    ‖a * momentTransform n R v 0‖ ≤ ‖a‖ * ‖v‖ := by
  change ‖a * v 0‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (norm_nonneg _)

end ThisWork
