module

public import ThisWork.Trajectory.Definitions
public import ThisWork.Lemma8

/-! Lemma 8 for arbitrary equal lower slopes.
Growth follows by exact reindexing. Independence follows from the normalized
moment limits along the cofinal subsequence, with the common argument factor canceled. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter
open scoped Topology

private theorem slope_reindex {m : ℕ} (hm : 0 < m) (A : ℝ) (n : ℕ) :
    (A / (m : ℝ)) * (m * n : ℕ) = A * n := by
  push_cast
  field_simp

private theorem complex_slope_reindex {m : ℕ} (hm : 0 < m) (A : ℝ) (n : ℕ) :
    ((A / (m : ℝ) : ℝ) : ℂ) * (m * n : ℕ) = (A : ℂ) * n := by
  exact_mod_cast slope_reindex hm A n

theorem kernel_equal_reindex {m : ℕ} (hm : 0 < m)
    (A₁ A₂ z : ℝ) (j : Branch) (n : ℕ) (x : ℂ) :
    kernel m 0 A₁ A₂ z j n x =
      ThisWork.kernel (A₁ / m) (A₂ / m) z j (m * n) x := by
  unfold kernel ThisWork.kernel
  rw [complex_slope_reindex hm A₁ n, complex_slope_reindex hm A₂ n]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_mul, pow_succ]

theorem branchIntegral_equal_reindex {m : ℕ} (hm : 0 < m)
    (A₁ A₂ z : ℝ) (j : Branch) (n : ℕ) :
    branchIntegral m 0 A₁ A₂ z j n =
      ThisWork.branchIntegral (A₁ / m) (A₂ / m) z j (m * n) := by
  funext k
  unfold branchIntegral ThisWork.branchIntegral
  simp_rw [kernel_equal_reindex hm, Nat.cast_mul]

private theorem gammaScale_reindex {m : ℕ} (hm : 0 < m) (A₁ A₂ : ℝ) (n : ℕ) :
    gammaScale (A₁ / m) (A₂ / m) (m * n) = gammaScale A₁ A₂ n := by
  simp only [gammaScale, slope_reindex hm]

private theorem rpow_scale_cancel {m : ℕ} (hm : 0 < m) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (n : ℕ) :
    saddleScale (A₁ / m) (A₂ / m) z * (m * n : ℕ) ^ (2 / 3 : ℝ) =
      saddleScale A₁ A₂ z * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hp : ((m : ℝ) ^ 2) ^ (1 / 3 : ℝ) = (m : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmR.le]
    norm_num
  simp only [saddleScale]
  rw [show A₁ / (m : ℝ) * (A₂ / m) * z = (A₁ * A₂ * z) / (m : ℝ) ^ 2 by ring,
    Real.div_rpow (mul_pos (mul_pos h₁ h₂) hz).le (sq_nonneg _), hp, Nat.cast_mul,
    Real.mul_rpow hmR.le (Nat.cast_nonneg n)]
  field_simp [(Real.rpow_pos_of_pos hmR (2 / 3 : ℝ)).ne']

/-- Lemma 8's growth conclusion for all equal lower slopes `(m,m,m)`. -/
theorem equal_normEstimate {m : ℕ} (hm : 0 < m) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (j : Branch) :
    ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
      ‖branchIntegral m 0 A₁ A₂ z j n‖ = equalScale m A₁ A₂ z n *
        Real.exp (-3 * saddleScale A₁ A₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E) := by
  obtain ⟨C, hC, N, hb⟩ := ThisWork.lemma8_normEstimate
    (div_pos h₁ (Nat.cast_pos.mpr hm)) (div_pos h₂ (Nat.cast_pos.mpr hm)) hz j
  refine ⟨C * (m : ℝ) ^ (1 / 3 : ℝ), mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    N, fun n hn => ?_⟩
  obtain ⟨E, hE, he⟩ := hb (m * n) (hn.trans (Nat.le_mul_of_pos_left n hm))
  refine ⟨E, by simpa only [Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_assoc] using hE, ?_⟩
  rw [branchIntegral_equal_reindex hm, he, gammaScale_reindex hm]
  have hs := rpow_scale_cancel hm h₁ h₂ hz n
  have heq : -3 * saddleScale (A₁ / m) (A₂ / m) z * (rho j).re *
      (m * n : ℕ) ^ (2 / 3 : ℝ) =
      -3 * saddleScale A₁ A₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) := by
    linear_combination -3 * (rho j).re * hs
  rw [heq, equalScale]

/-- Independence along the cofinal subsequence `N = m*n` follows from the
normalized moment limits, rather than from sequence independence alone. -/
theorem equal_linearIndependent {m : ℕ} (hm : 0 < m) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    LinearIndependent ℂ (fun j : Branch => branchIntegral m 0 A₁ A₂ z j) := by
  let : PositiveArgument := ⟨z, hz⟩
  let : Fintype Branch := Fintype.ofEquiv (Fin 3) Analytic.branchEquiv
  have hα₁ : 0 < A₁ / (m : ℝ) := div_pos h₁ (Nat.cast_pos.mpr hm)
  have hα₂ : 0 < A₂ / (m : ℝ) := div_pos h₂ (Nat.cast_pos.mpr hm)
  let S : ∀ j, Analytic.CompactSaddleFamily (A₁ / m) (A₂ / m) j :=
    fun j => (Analytic.exists_compactSaddleFamily hα₁ hα₂ j).some
  let D : ∀ j, (S j).LocalSaddleData := fun j => ((S j).exists_localSaddleData hα₁ hα₂).some
  have hr : Tendsto (fun n : ℕ => m * n) atTop atTop := by
    refine tendsto_atTop.mpr (fun N => ?_)
    exact eventually_atTop.mpr ⟨N, fun n hn => hn.trans (Nat.le_mul_of_pos_left n hm)⟩
  apply Analytic.linearIndependent_branches_of_moment_limits (Analytic.saddleScale_pos hα₁ hα₂)
    (fun n => Analytic.momentTransform (m * n) (Analytic.largeScale (m * n)))
    (fun n j => (D j).normalizingScalar (m * n) *
      Complex.exp (-(((m * n : ℕ) : ℂ) * (Real.log z : ℂ))))
  · exact Filter.eventually_all.mpr (fun j =>
      (hr.eventually ((D j).eventually_normalizingScalar_ne_zero hα₁ hα₂)).mono
        (fun n hn => mul_ne_zero hn (Complex.exp_ne_zero _)))
  · intro j k
    have hlim := ((D j).normalized_originalMoment_tendsto hα₁ hα₂ k).comp hr
    apply hlim.congr'
    filter_upwards [] with n
    rw [branchIntegral_equal_reindex hm, ThisWork.branchIntegral_factor hz, LinearMap.map_smul]
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Complex.exp_neg, mul_assoc, inv_mul_cancel_left₀ (Complex.exp_ne_zero _)]

/-- Lemma 8, including growth and independence, for every equal lower slope `m ≥ 1`
and every positive real Meijer G argument. -/
theorem equal_lemma8 {m : ℕ} (hm : 0 < m) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    (∀ j : Branch, ∃ C ≥ 0, ∃ N : ℕ, ∀ n ≥ N, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 / 3 : ℝ) ∧
      ‖branchIntegral m 0 A₁ A₂ z j n‖ = equalScale m A₁ A₂ z n *
        Real.exp (-3 * saddleScale A₁ A₂ z * (rho j).re * (n : ℝ) ^ (2 / 3 : ℝ) + E)) ∧
    LinearIndependent ℂ (fun j : Branch => branchIntegral m 0 A₁ A₂ z j) :=
  ⟨equal_normEstimate hm h₁ h₂ hz, equal_linearIndependent hm h₁ h₂ hz⟩

end ThisWork.Trajectory
