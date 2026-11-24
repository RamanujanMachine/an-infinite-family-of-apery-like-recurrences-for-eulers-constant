module

public import ThisWork.HigherRank.MomentTranslation

/-! Polynomial conditioning of the exact change of moment center. -/

@[expose] public section
namespace ThisWork.HigherRank

noncomputable def translateMoments (r : ℕ) (w : ℂ) (v : Fin r → ℂ) : Fin r → ℂ := fun k =>
  ∑ i : Fin (k.val + 1), w ^ (k.val - i.val) * (k.val.choose i.val : ℂ) *
    v ⟨i.val, by omega⟩

noncomputable def translateMomentsLinear (r : ℕ) (w : ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun := translateMoments r w
  map_add' := by
    intro v u
    funext k
    simp only [translateMoments, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    funext k
    simp only [translateMoments, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem norm_translateMoments_le (r : ℕ) (w : ℂ) (v : Fin r → ℂ) :
    ‖translateMoments r w v‖ ≤ (1 + ‖w‖) ^ (r - 1) * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  change ‖∑ i : Fin (k.val + 1), _‖ ≤ _
  calc
    _ ≤ ∑ i : Fin (k.val + 1),
        ‖w‖ ^ (k.val - i.val) * (k.val.choose i.val : ℝ) * ‖v‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v _) (by positivity)
    _ = (1 + ‖w‖) ^ k.val * ‖v‖ := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range
        (fun i => ‖w‖ ^ (k.val - i) * (k.val.choose i : ℝ)) (k.val + 1), add_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [norm_nonneg w]) (by omega)) (norm_nonneg v)

theorem branchIntegral_change_center {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i)
    (b q : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) :
    branchIntegral r b A z j n =
      Complex.exp ((Real.log z : ℂ) * (((b : ℂ) - q) * n)) •
        translateMoments r (((b : ℂ) - q) * n) (branchIntegral r q A z j n) := by
  funext k
  have h := momentIntegral_change_center hr hA b q z j n k.val
  rw [momentIntegral_eq_component] at h
  change branchIntegral r b A z j n k =
    Complex.exp ((Real.log z : ℂ) * (((b : ℂ) - q) * n)) *
      translateMoments r (((b : ℂ) - q) * n) (branchIntegral r q A z j n) k
  rw [h]
  congr 1
  rw [Finset.sum_range]
  rfl

theorem norm_branchIntegral_change_center_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i)
    (b q : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) :
    ‖branchIntegral r b A z j n‖ ≤
      Real.exp (Real.log z * (((b : ℝ) - q) * n)) *
        (1 + ‖((b : ℂ) - q) * n‖) ^ (r - 1) * ‖branchIntegral r q A z j n‖ := by
  rw [branchIntegral_change_center hr hA b q z j n, norm_smul,
    Complex.norm_exp]
  have hre : (((Real.log z : ℂ) * (((b : ℂ) - q) * n))).re =
      Real.log z * (((b : ℝ) - q) * n) := by simp
  rw [hre]
  exact (mul_le_mul_of_nonneg_left (norm_translateMoments_le _ _ _)
    (Real.exp_pos _).le).trans_eq (by ring)

end ThisWork.HigherRank
