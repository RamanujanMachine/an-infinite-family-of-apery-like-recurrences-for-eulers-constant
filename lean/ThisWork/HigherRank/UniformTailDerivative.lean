module

public import ThisWork.HigherRank.SaddleEquation
public import ThisWork.UniformTailDerivative

/-! Uniform large-index bounds on the entire horizontal tails. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_re_exactSaddleEquation_left_lower {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η H : ℝ} (hη : 0 < η)
    (z : ℝ) (j : ℤ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ y : ℝ, η ≤ |y| → |y| ≤ H →
      Real.log t - C ≤ (exactSaddleEquation r A z j n (-(t : ℂ) + (y : ℂ) * Complex.I)).re := by
  let D := 1 + 9 / η + 4 * Real.pi
  let C := (∑ i, Real.log (A i + H + 2)) + (r : ℝ) * D + ((r : ℝ) - 1) + |Real.log z|
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  have hupper : ∀ᶠ n : ℕ in atTop, ∀ i, 4 ≤ A i * n :=
    Filter.eventually_all.mpr (fun i => (eventually_affine_conditions (by omega : 0 < r) (hA i) 0).mono
      (fun _ h => h.1))
  filter_upwards [uniform_scaled_digamma_im_smallParameter hr hη, hupper,
    (largeScale_tendsto (show 1 < r by omega)).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hψ hupper hR hn t ht y hy hyH
  have hRn : largeScale r n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le
    (by exact_mod_cast hn) (by linarith [div_nonneg zero_le_one (Nat.cast_nonneg r : (0 : ℝ) ≤ r)] : 1 - 1 / (r : ℝ) ≤ 1)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hb : ‖Complex.digamma ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.log ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤ D := by
    exact (hψ _ (by simpa using hy)).trans
      (mul_le_of_le_one_right hD (smallParameter_le_one r hn))
  have hleft := Analytic.re_digamma_left_tail_ge hR ht hb
  have hu (i : Fin (r - 1)) := Analytic.re_digamma_right_tail_le (hA i).le
    (show 0 ≤ largeScale r n by linarith) hRn hn ht hyH (hupper i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hlog := log_largeScale (by omega : 0 < r) (by omega : 0 < n)
  have hC := le_max_right 0 C
  simp only [exactSaddleEquation, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.re_sum, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, sub_zero, add_zero]
  dsimp only [C] at hC ⊢
  nlinarith [le_abs_self (Real.log z)]

end ThisWork.HigherRank
