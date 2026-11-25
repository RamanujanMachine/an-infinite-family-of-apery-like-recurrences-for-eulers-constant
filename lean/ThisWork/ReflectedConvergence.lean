module

public import ThisWork.BoundaryTails
public import ThisWork.RectangleDeformation

/-! Real-axis and bank convergence of the even-rank reflected kernel.
The bounds are deduced from the proved Fourier identity, without residues. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

theorem uniform_reflected_real_left_decay {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (b : ℕ) (z : ℝ) (n : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ‖reflectedKernel r b A z n (-(T : ℂ))‖ ≤ Real.exp (-q * T) := by
  let D := Real.exp 1 / Real.pi
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  filter_upwards [uniform_weighted_boundary_left_decay hr hA (H := 1) le_rfl half hrh b z n 0 (q + 1),
    eventually_ge_atTop (6 * (r : ℝ)), eventually_ge_atTop D] with T hn hT hTD
  have hb := hn (-1) (by norm_num) (by norm_num)
  simp only [pow_zero, one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, ← sub_eq_add_neg] at hb
  have hreal := norm_reflectedKernel_real_le_boundary hr hA b z n (x := -T) (by linarith)
  simp only [Complex.ofReal_neg] at hreal
  have hDe : D ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  calc
    _ ≤ D * ‖boundaryKernel r b A z n (-(T : ℂ) - Complex.I)‖ := hreal
    _ ≤ D * Real.exp (-(q + 1) * T) := mul_le_mul_of_nonneg_left (by simpa only [neg_mul] using hb) hD
    _ ≤ Real.exp T * Real.exp (-(q + 1) * T) := mul_le_mul_of_nonneg_right hDe (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem uniform_reflected_strip_left_decay {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (b : ℕ) (z : ℝ) (n : ℕ) (q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ y : ℝ, |y| ≤ 1 →
      ‖reflectedKernel r b A z n (-(T : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (-q * T) := by
  filter_upwards [uniform_reflected_real_left_decay hr hA half hrh b z n (q + 1),
    eventually_ge_atTop (6 * (r : ℝ)), eventually_ge_atTop (1 : ℝ)] with T hn hT hT1 y hy
  have hbank := norm_reflectedKernel_fixed_bank_le hr hA b z n (x := -T) (by linarith) hy
  simp only [Complex.ofReal_neg] at hbank
  calc
    _ ≤ ‖reflectedKernel r b A z n (-(T : ℂ))‖ * Real.exp 1 := hbank
    _ ≤ Real.exp (-(q + 1) * T) * Real.exp 1 := mul_le_mul_of_nonneg_right hn (Real.exp_pos 1).le
    _ = Real.exp (-(q + 1) * T + 1) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem integrableOn_reflectedKernel_horizontal {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (b : ℕ) (z : ℝ) (n : ℕ) {right y : ℝ} (hright : right < 1) (hy : |y| ≤ 1) :
    IntegrableOn (fun u : ℝ => reflectedKernel r b A z n ((u : ℂ) + (y : ℂ) * Complex.I)) (Iic right) := by
  apply Analytic.integrableOn_Iic_of_exp_bound
  · intro u hu
    have hd := differentiableAt_reflectedKernel_of_re_lt_one hA b z n
      (x := (u : ℂ) + (y : ℂ) * Complex.I) (by simpa [Complex.mul_re] using hu.trans_lt hright)
    exact (hd.continuousAt.comp (f := fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop)).continuousWithinAt
  have h := tendsto_neg_atBot_atTop.eventually (uniform_reflected_strip_left_decay hr hA half hrh b z n 1)
  exact h.mono (fun u hu => by simpa using hu y hy)

theorem tendsto_reflected_left_bridge_zero {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (b : ℕ) (z : ℝ) (n : ℕ) {a auxB : ℝ} (hstrip : ∀ y ∈ uIcc a auxB, |y| ≤ 1) :
    Tendsto (fun T : ℝ => ∫ y in a..auxB, Complex.I *
      reflectedKernel r b A z n (-(T : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun T => Real.exp (-T) * |auxB - a|)
  · filter_upwards [uniform_reflected_strip_left_decay hr hA half hrh b z n 1] with T hn
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    simpa only [norm_mul, Complex.norm_I, one_mul, neg_mul] using hn y (hstrip y (uIoc_subset_uIcc hy))
  · simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const |auxB - a|

end ThisWork
