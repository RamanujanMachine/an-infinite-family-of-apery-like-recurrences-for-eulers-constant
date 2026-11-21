module

public import ThisWork.Trajectory.Reflection

/-! The elementary combination is an actual reflected Hankel integral, with
linearity justified by the proved absolute convergence of every defining branch. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set

theorem reference_sin_ne_zero {x : ℂ} (hx : x ∈ Analytic.hankelTrace (1 / 2) 1) :
    Complex.sin ((Real.pi : ℂ) * x) ≠ 0 := by
  have hΓ := Complex.Gamma_ne_zero (Analytic.not_neg_nat_of_mem_slitPlane
    (Analytic.hankelTrace_mem_slitPlane (by norm_num) (by norm_num) hx))
  have hright : Complex.Gamma (1 - x) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    have h := Analytic.hankelTrace_re_le hx
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  intro hs
  have h := Complex.Gamma_mul_Gamma_one_sub x
  rw [hs, div_zero] at h
  exact mul_ne_zero hΓ hright h

theorem elementaryIntegral_eq_reflected {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m d n : ℕ) :
    elementaryIntegral m d A₁ A₂ z n = fun k : Fin 3 =>
      -4 * (Real.pi : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        hankelIntegral (1 / 2) 1 (fun x => ((m : ℂ) * n - x) ^ k.val *
          reflectedKernel m d A₁ A₂ z n x) := by
  funext k
  have href : (1 / 2 : ℝ) < min (A₁ * n + 1) (A₂ * n + 1) := by
    apply lt_min <;> nlinarith [mul_nonneg h₁.le (Nat.cast_nonneg (α := ℝ) n),
      mul_nonneg h₂.le (Nat.cast_nonneg (α := ℝ) n)]
  have hi := fun j => weighted_hankel_integrable hz h₁ h₂ m d j n k.val
    (by norm_num : (0 : ℝ) < 1 / 2) href le_rfl
  have he : EqOn
      (fun x => ((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z .one n x +
        ((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z .two n x -
        2 * (((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z .three n x))
      (fun x => -4 * (Real.pi : ℂ) ^ 2 *
        (((m : ℂ) * n - x) ^ k.val * reflectedKernel m d A₁ A₂ z n x))
      (Analytic.hankelTrace (1 / 2) 1) := by
    intro x hx
    linear_combination ((m : ℂ) * n - x) ^ k.val * kernel_branch_cancellation m d A₁ A₂ z n x +
      ((m : ℂ) * n - x) ^ k.val * kernel_reflection m d A₁ A₂ z n (reference_sin_ne_zero hx)
  have hsum := Analytic.hankelIntegral_congr (show (0 : ℝ) ≤ 1 by norm_num) he
  rw [Analytic.hankelIntegral_sub ((hi .one).add (hi .two)) ((hi .three).const_mul 2),
    Analytic.hankelIntegral_add (hi .one) (hi .two),
    Analytic.hankelIntegral_const_mul, Analytic.hankelIntegral_const_mul] at hsum
  simp only [elementaryIntegral, Pi.add_apply, Pi.sub_apply, two_smul, branchIntegral]
  linear_combination (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hsum

end ThisWork.Trajectory
