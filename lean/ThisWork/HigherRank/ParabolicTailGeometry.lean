module

public import ThisWork.HigherRank.ParabolicContour

/-! A single finite cutoff places both parabolic endpoints in the left
cone, uniformly under translations of norm at most one. -/

@[expose] public section
namespace ThisWork.HigherRank

theorem exists_parabolic_cone_cutoff {a : ℝ} (ha : 0 < a) (T b h : ℝ) :
    ∃ B > 0, |b| + |h| + 1 ≤ B ∧ ∀ δ : ℂ, ‖δ‖ ≤ 1 →
      T ≤ B ^ 2 - a ^ 2 - δ.re ∧
      ∀ e : ℝ, (e = 1 ∨ e = -1) →
        1 ≤ |δ.im + e * (2 * a * B)| ∧ |δ.im + e * (2 * a * B)| ≤ B ^ 2 - a ^ 2 - δ.re := by
  let B := max (|T| + 2 * a ^ 2 + 3)
    (max (4 * a + 4) (max (1 / a + 1) (|b| + |h| + 1)))
  have hBT : |T| + 2 * a ^ 2 + 3 ≤ B := le_max_left _ _
  have hBa : 4 * a + 4 ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBi : 1 / a + 1 ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBb : |b| + |h| + 1 ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hB : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hAB : 1 ≤ a * B := by
    have hx : 1 / a ≤ B := by linarith
    have hy := (div_le_iff₀ ha).mp hx
    nlinarith
  refine ⟨B, hB, hBb, ?_⟩
  intro δ hδ
  have hre := (Complex.abs_re_le_norm δ).trans hδ
  have him := (Complex.abs_im_le_norm δ).trans hδ
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have haB : a ^ 2 ≤ a * B := by nlinarith
  have hcone : 2 * a * B + 1 ≤ B ^ 2 - a ^ 2 - δ.re := by
    nlinarith [mul_le_mul_of_nonneg_right hBa hB.le, (abs_le.mp hre).2]
  refine ⟨by nlinarith [le_abs_self T, (abs_le.mp hre).2], ?_⟩
  intro e he
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have heH : |e * (2 * a * B)| = 2 * a * B := by
    rw [abs_mul, heabs, one_mul, abs_of_nonneg (by positivity)]
  have hl := abs_add_le δ.im (e * (2 * a * B))
  have hr := norm_sub_norm_le (e * (2 * a * B)) (-δ.im)
  simp only [Real.norm_eq_abs, abs_neg, sub_neg_eq_add] at hr
  rw [heH] at hl hr
  rw [add_comm (e * (2 * a * B)) δ.im] at hr
  exact ⟨by linarith, by linarith⟩

end ThisWork.HigherRank
