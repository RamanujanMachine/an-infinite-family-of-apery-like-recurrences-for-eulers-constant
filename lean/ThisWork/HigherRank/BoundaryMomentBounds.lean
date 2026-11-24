module

public import ThisWork.HigherRank.BoundaryGrowth
public import ThisWork.HigherRank.IntegratedTails

/-! Polynomial weights on the fixed even-rank Hankel banks. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem norm_boundaryKernel_fixed_bank_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ)
    {x y : ℝ} (hx : x ≤ -(6 * (r : ℝ))) (hy : y = 1 ∨ y = -1) :
    ‖boundaryKernel r b A z n ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (2 * Real.pi * Real.exp 1 + Real.pi / 4) * ‖reflectedKernel r b A z n (x : ℂ)‖ := by
  obtain ⟨hp, hm⟩ := fixed_boundary_bank_errors_le hr hA b z n hx
  rcases hy with rfl | rfl
  · simp only [Complex.ofReal_one, one_mul]
    exact hp.trans (mul_le_mul_of_nonneg_right (by linarith [mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) (Real.exp_pos 1).le]) (norm_nonneg _))
  · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg]
    have hbank := norm_reflectedKernel_fixed_bank_le hr hA b z n hx (h := -1) (by norm_num)
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] at hbank
    have ht := norm_add_le
      (boundaryKernel r b A z n ((x : ℂ) - Complex.I) -
        2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r b A z n ((x : ℂ) - Complex.I))
      (2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r b A z n ((x : ℂ) - Complex.I))
    rw [sub_add_cancel] at ht
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_I, mul_one] at ht
    nlinarith [mul_le_mul_of_nonneg_left hbank (show 0 ≤ 2 * Real.pi by positivity)]

theorem weighted_boundary_bank_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (n k : ℕ)
    {x y : ℝ} (hx : x ≤ -(6 * (r : ℝ))) (hy : y = 1 ∨ y = -1) :
    ‖(-((x : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      boundaryKernel r 0 A z n ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (2 * Real.pi * Real.exp 1 + Real.pi / 4) * (1 + |x|) ^ k *
        ‖reflectedKernel r 0 A z n (x : ℂ)‖ := by
  have hb := norm_boundaryKernel_fixed_bank_le hr hA 0 z n hx hy
  have hn : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ 1 + |x| := by
    have hy1 : |y| = 1 := by rcases hy with rfl | rfl <;> norm_num
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      hy1, add_comm] using norm_add_le (x : ℂ) ((y : ℂ) * Complex.I)
  rw [norm_mul, norm_pow, norm_neg]
  exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn k) hb
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

end ThisWork.HigherRank
