module

public import ThisWork.HigherRank.HankelTails
public import ThisWork.HigherRank.FixedBoundaryBanks

/-! Absolute left-tail decay of the even-rank boundary combination, deduced
from its proved finite Fourier identity and the original Gamma-kernel tails. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_weighted_boundary_left_decay {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {H : ℝ} (hH : 1 ≤ H)
    (half : ℕ) (hrh : r = 2 * half) (m : ℕ) (z : ℝ) (n k : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      ‖(((m : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I)) ^ k) *
        boundaryKernel r m A z n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (-q * T) := by
  let L : ℂ := (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1)
  let a : ℕ → ℂ := fun i => (-1 : ℂ) ^ i * ((r - 1).choose i : ℂ)
  let C : ℝ := ‖L⁻¹‖ * ∑ i ∈ Finset.range r, ‖a i‖
  have hL : L ≠ 0 := pow_ne_zero _ (mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hK : ∀ᶠ T : ℝ in atTop, ∀ i : Fin r, ∀ y : ℝ, 1 ≤ |y| → |y| ≤ H →
      ‖(((m : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I)) ^ k) *
        kernel r m A z ((half : ℤ) - i.val) n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          Real.exp (-(q + 1) * T) :=
    Filter.eventually_all.mpr (fun i => uniform_weighted_kernel_left_decay hr hA hH m z _ n k (q + 1))
  filter_upwards [hK, eventually_ge_atTop C] with T hT hTC y hy hyH
  let x : ℂ := -(T : ℂ) + (y : ℂ) * Complex.I
  let w : ℂ := ((m : ℂ) * n - x) ^ k
  have hsin : Complex.sin ((Real.pi : ℂ) * x) ≠ 0 := sin_pi_ne_zero_of_im_ne_zero
    (by
      intro he
      have hi : y = 0 := by
        simpa only [x, Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
          mul_zero, add_zero, zero_add] using he
      norm_num [hi] at hy)
  have hfourier := even_boundary_kernel_fourier hr half hrh m A z n hsin
  have he : w * boundaryKernel r m A z n x =
      L⁻¹ * ∑ i ∈ Finset.range r, a i * (w * kernel r m A z ((half : ℤ) - i) n x) := by
    have hs : (∑ i ∈ Finset.range r, a i * (w * kernel r m A z ((half : ℤ) - i) n x)) =
        w * ∑ i ∈ Finset.range r, a i * kernel r m A z ((half : ℤ) - i) n x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hf : (∑ i ∈ Finset.range r, a i * kernel r m A z ((half : ℤ) - i) n x) =
        L * boundaryKernel r m A z n x := hfourier.symm
    rw [hs, hf]
    field_simp
  have hbound : ‖w * boundaryKernel r m A z n x‖ ≤ C * Real.exp (-(q + 1) * T) := by
    rw [he, norm_mul]
    calc
      _ ≤ ‖L⁻¹‖ * ∑ i ∈ Finset.range r, ‖a i * (w * kernel r m A z ((half : ℤ) - i) n x)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ ‖L⁻¹‖ * ∑ i ∈ Finset.range r, ‖a i‖ * Real.exp (-(q + 1) * T) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hT ⟨i, Finset.mem_range.mp hi⟩ y hy hyH) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; dsimp only [C]; ring
  have hCe : C ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  exact hbound.trans ((mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le).trans_eq (by
    rw [← Real.exp_add]
    congr 1
    ring))

end ThisWork.HigherRank
