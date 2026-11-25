module

public import ThisWork.OffCutNoncancellation

/-! Quantitative noncancellation survives exact polynomial recentering. -/

@[expose] public section
namespace ThisWork

open Set Filter
open scoped Topology

theorem offCut_noncancellation {r d : ℕ} (hr : 3 ≤ r) (hd : d ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (J : Fin d → ℤ) (θ : Fin d → ℝ) (hθ : ∀ i, θ i ∈ Ioo (-Real.pi) Real.pi)
    (hj : ∀ i, (r : ℝ) * θ i = -2 * Real.pi * J i)
    (hinj : Function.Injective θ) :
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ a : Fin d → ℂ, ∀ j : Fin d,
      ‖a j‖ * ‖branchIntegral r b A z (J j) n‖ ≤
        K * (n : ℝ) ^ (3 * (r - 1)) * ‖∑ i, a i • branchIntegral r b A z (J i) n‖ := by
  obtain ⟨K, hK, hb⟩ := offCut_zeroCenter_noncancellation hr hd hA hz J θ hθ hj hinj
  refine ⟨K * (1 + (b : ℝ)) ^ (2 * (r - 1)), by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1 a j
  let c := Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n))
  let w : ℂ := (b : ℂ) * n
  let P := (1 + (b : ℝ) * n) ^ (r - 1)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hwn : ‖w‖ = (b : ℝ) * n := by simp only [w, norm_mul, Complex.norm_natCast]
  have hp (i : Fin d) : branchIntegral r b A z (J i) n =
      c • translateMoments r w (branchIntegral r 0 A z (J i) n) := by
    simpa only [Nat.cast_zero, sub_zero, c, w] using
      branchIntegral_change_center (by omega : 0 < r) hA b 0 z (J i) n
  have hm (i : Fin d) : branchIntegral r 0 A z (J i) n =
      c⁻¹ • translateMoments r (-w) (branchIntegral r b A z (J i) n) := by
    simpa only [Nat.cast_zero, zero_sub, neg_mul, mul_neg, Complex.exp_neg, c, w] using
      branchIntegral_change_center (by omega : 0 < r) hA 0 b z (J i) n
  have hpbound : ‖branchIntegral r b A z (J j) n‖ ≤
      ‖c‖ * P * ‖branchIntegral r 0 A z (J j) n‖ := by
    rw [hp j, norm_smul]
    have h := mul_le_mul_of_nonneg_left (norm_translateMoments_le r w
      (branchIntegral r 0 A z (J j) n)) (norm_nonneg c)
    simpa only [hwn, mul_assoc] using h
  have hsum : (∑ i, a i • branchIntegral r 0 A z (J i) n) =
      c⁻¹ • translateMoments r (-w) (∑ i, a i • branchIntegral r b A z (J i) n) := by
    change _ = (c⁻¹ • translateMomentsLinear r (-w)) _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    exact congrArg (a i • ·) (hm i)
  have hsumBound : ‖∑ i, a i • branchIntegral r 0 A z (J i) n‖ ≤
      ‖c⁻¹‖ * P * ‖∑ i, a i • branchIntegral r b A z (J i) n‖ := by
    rw [hsum, norm_smul]
    have h := mul_le_mul_of_nonneg_left (norm_translateMoments_le r (-w)
      (∑ i, a i • branchIntegral r b A z (J i) n)) (norm_nonneg c⁻¹)
    simpa only [norm_neg, hwn, mul_assoc] using h
  have hPn : P ≤ (1 + (b : ℝ)) ^ (r - 1) * (n : ℝ) ^ (r - 1) := by
    dsimp only [P]
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ (‖c‖ * P) * (‖a j‖ * ‖branchIntegral r 0 A z (J j) n‖) :=
      (mul_le_mul_of_nonneg_left hpbound (norm_nonneg _)).trans_eq (by ring)
    _ ≤ (‖c‖ * P) * (K * (n : ℝ) ^ (r - 1) * ‖∑ i, a i • branchIntegral r 0 A z (J i) n‖) :=
      mul_le_mul_of_nonneg_left (hn a j) (by positivity)
    _ ≤ (‖c‖ * P) * (K * (n : ℝ) ^ (r - 1) *
        (‖c⁻¹‖ * P * ‖∑ i, a i • branchIntegral r b A z (J i) n‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumBound (by positivity)) (by positivity)
    _ = K * (n : ℝ) ^ (r - 1) * P ^ 2 * ‖∑ i, a i • branchIntegral r b A z (J i) n‖ := by
      rw [norm_inv]
      field_simp
    _ ≤ K * (n : ℝ) ^ (r - 1) * ((1 + (b : ℝ)) ^ (r - 1) * (n : ℝ) ^ (r - 1)) ^ 2 *
        ‖∑ i, a i • branchIntegral r b A z (J i) n‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP hPn 2)
        (by positivity)) (norm_nonneg _)
    _ = _ := by
      simp only [show 3 * (r - 1) = (r - 1) + (r - 1) + (r - 1) by omega,
        show 2 * (r - 1) = (r - 1) * 2 by omega, pow_add, pow_mul, mul_pow]
      ring

end ThisWork
