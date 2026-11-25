module

public import ThisWork.HankelDeformation

/-! Independent upper and lower Hankel heights. This permits translations
to the exact moving saddle without imposing symmetry about the real axis. -/

@[expose] public section
namespace ThisWork

open Set Filter MeasureTheory
open scoped Topology

noncomputable def asymmetricHankelIntegral (right low high : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ u in Iic right, f ((u : ℂ) + (low : ℂ) * Complex.I)) +
    (∫ y in low..high, Complex.I * f ((right : ℂ) + (y : ℂ) * Complex.I)) -
    ∫ u in Iic right, f ((u : ℂ) + (high : ℂ) * Complex.I)

theorem weighted_hankel_eq_asymmetric {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    {right low high : ℝ} (hright0 : 0 < right) (hright : ∀ i, right < A i * n + 1)
    (hlow : low ≤ -1) (hhigh : 1 ≤ high) :
    hankelIntegral right 1 (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x) =
      asymmetricHankelIntegral right low high
        (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x) := by
  have hlow' : 1 ≤ -low := by linarith
  have hlo := weighted_horizontal_tail_deformation hr hA
    (H := max 1 (-low)) (le_max_left _ _) b z j n k hright
    (a := -1) (auxB := low) (fun y hy => by
      have h := Analytic.negative_height_strip le_rfl hlow' (v := y) (by simpa using hy)
      simpa using h)
  have hhi := weighted_horizontal_tail_deformation hr hA
    (H := max 1 high) (le_max_left _ _) b z j n k hright
    (a := 1) (auxB := high) (fun y hy => Analytic.positive_height_strip le_rfl hhigh hy)
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright low (-1))
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright (-1) 1)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright low 1)
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright 1 high)
  rw [intervalIntegral.integral_symm low (-1)] at hlo
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] at hlo hhi
  dsimp only [hankelIntegral, asymmetricHankelIntegral]
  simp only [Complex.ofReal_one, one_mul]
  linear_combination hlo - hhi + h₁ + h₂

theorem branchIntegral_eq_asymmetric {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) (k : Fin r)
    {right low high : ℝ} (hright0 : 0 < right) (hright : ∀ i, right < A i * n + 1)
    (hlow : low ≤ -1) (hhigh : 1 ≤ high) :
    branchIntegral r b A z j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      asymmetricHankelIntegral right low high
        (fun x => ((b : ℂ) * n - x) ^ k.val * kernel r b A z j n x) := by
  rw [branchIntegral_eq_deformed hr hA b z j n k hright0 hright le_rfl,
    weighted_hankel_eq_asymmetric hr hA b z j n k.val hright0 hright hlow hhigh]

end ThisWork
