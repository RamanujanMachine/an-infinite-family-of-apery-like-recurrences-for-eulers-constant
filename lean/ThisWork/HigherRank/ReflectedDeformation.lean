module

public import ThisWork.HigherRank.ReflectedConvergence

/-! The reflected lower bank can be moved to the positive real integral.
All rectangles lie in the pole-free half-plane `re < 1`. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter MeasureTheory
open scoped Topology

theorem reflected_horizontal_tail_deformation {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (b : ℕ) (z : ℝ) (n : ℕ) {right a auxB : ℝ} (hright : right < 1)
    (hstrip : ∀ y ∈ uIcc a auxB, |y| ≤ 1) :
    (∫ u in Iic right, reflectedKernel r b A z n ((u : ℂ) + (a : ℂ) * Complex.I)) -
      (∫ u in Iic right, reflectedKernel r b A z n ((u : ℂ) + (auxB : ℂ) * Complex.I)) +
      (∫ y in a..auxB, Complex.I * reflectedKernel r b A z n ((right : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
  apply Analytic.horizontal_tail_identity_of_rectangles
    (integrableOn_reflectedKernel_horizontal hr hA half hrh b z n hright (hstrip a left_mem_uIcc))
    (integrableOn_reflectedKernel_horizontal hr hA half hrh b z n hright (hstrip auxB right_mem_uIcc))
    (tendsto_reflected_left_bridge_zero hr hA half hrh b z n hstrip)
  filter_upwards [eventually_ge_atTop (-right)] with T hT
  have hd : DifferentiableOn ℂ (reflectedKernel r b A z n) {x : ℂ | x.re < 1} :=
    fun x hx => (differentiableAt_reflectedKernel_of_re_lt_one hA b z n hx).differentiableWithinAt
  convert Analytic.rectangle_integral_identity hd (a := -T) (r := right) (A := a) (B := auxB)
    (fun x hx _ => (show x.re ≤ right by
      simpa only [max_eq_right (show -T ≤ right by linarith)] using hx.2).trans_lt hright) using 1
  simp only [Complex.ofReal_neg]

theorem reflected_lower_bank_eq_real {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (b : ℕ) (z : ℝ) (n : ℕ) {right : ℝ} (hright : right < 1) :
    (∫ u in Iic right, reflectedKernel r b A z n ((u : ℂ) - Complex.I)) =
      (∫ u in Iic right, reflectedKernel r b A z n (u : ℂ)) -
      (∫ y in (-1 : ℝ)..0, Complex.I * reflectedKernel r b A z n ((right : ℂ) + (y : ℂ) * Complex.I)) := by
  have h := reflected_horizontal_tail_deformation hr hA half hrh b z n hright
    (a := -1) (auxB := 0) (fun y hy => by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hy
      exact abs_le.mpr ⟨hy.1, by linarith [hy.2]⟩)
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
    ← sub_eq_add_neg, Complex.ofReal_zero, zero_mul, add_zero] at h
  linear_combination h

end ThisWork.HigherRank
