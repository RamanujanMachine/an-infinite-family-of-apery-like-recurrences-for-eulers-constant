module

public import ThisWork.HigherRank.AbsoluteConvergence
public import ThisWork.HankelDeformation

/-! Deformation of the actual arbitrary-rank integrals between admissible
polygonal Hankel contours. Every infinite-tail limit is justified. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter MeasureTheory
open scoped Topology

theorem weighted_horizontal_tail_deformation {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {right H a auxB : ℝ} (hH : 1 ≤ H)
    (b : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ) (hright : ∀ i, right < A i * n + 1)
    (hstrip : ∀ y ∈ uIcc a auxB, 1 ≤ |y| ∧ |y| ≤ H) :
    (∫ u in Iic right, ((b : ℂ) * n - ((u : ℂ) + (a : ℂ) * Complex.I)) ^ k *
      kernel r b A z j n ((u : ℂ) + (a : ℂ) * Complex.I)) -
    (∫ u in Iic right, ((b : ℂ) * n - ((u : ℂ) + (auxB : ℂ) * Complex.I)) ^ k *
      kernel r b A z j n ((u : ℂ) + (auxB : ℂ) * Complex.I)) +
    (∫ y in a..auxB, Complex.I * (((b : ℂ) * n - ((right : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      kernel r b A z j n ((right : ℂ) + (y : ℂ) * Complex.I))) = 0 := by
  refine Analytic.horizontal_tail_identity_of_rectangles
    (f := fun x : ℂ => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x)
    (r := right) (A := a) (B := auxB)
    (integrableOn_weighted_kernel_horizontal hr hA b z j n k hright (hstrip a left_mem_uIcc).1)
    (integrableOn_weighted_kernel_horizontal hr hA b z j n k hright (hstrip auxB right_mem_uIcc).1)
    (tendsto_left_bridge_zero hr hA hH b z j n k hstrip) ?_
  filter_upwards [eventually_ge_atTop (-right)] with T hT
  convert Analytic.rectangle_integral_identity (differentiableOn_weighted_kernel r b A z j n k)
    (a := -T) (r := right) (A := a) (B := auxB) ?_ using 1
  · simp only [Complex.ofReal_neg]
  intro x hxre hxim
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by
    have h := (hstrip x.im hxim).1
    intro he
    norm_num [he] at h)), ?_⟩
  intro i
  exact (show x.re ≤ right by simpa only [max_eq_right (show -T ≤ right by linarith)] using hxre.2).trans_lt (hright i)

theorem weighted_hankel_height_eq {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    {right a auxB : ℝ} (hright0 : 0 < right) (hright : ∀ i, right < A i * n + 1)
    (ha : 1 ≤ a) (hb : 1 ≤ auxB) :
    hankelIntegral right a (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x) =
      hankelIntegral right auxB (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x) := by
  have hlo := weighted_horizontal_tail_deformation hr hA (H := max auxB a)
    (hb.trans (le_max_left auxB a)) b z j n k hright
    (a := -auxB) (auxB := -a) (fun y hy => Analytic.negative_height_strip hb ha hy)
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hlo
  have hhi := weighted_horizontal_tail_deformation hr hA (H := max a auxB)
    (ha.trans (le_max_left a auxB)) b z j n k hright
    (a := a) (auxB := auxB) (fun y hy => Analytic.positive_height_strip ha hb hy)
  have hvleft := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright (-auxB) (-a))
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright (-a) a)
  have hvright := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright (-auxB) a)
    (intervalIntegrable_weighted_kernel_vertical b z j n k hright0 hright a auxB)
  dsimp only [hankelIntegral]
  linear_combination -hlo - hhi + hvleft + hvright

theorem weighted_hankel_right_eq {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    {right s height : ℝ} (hright0 : 0 < right) (hs0 : 0 < s)
    (hright : ∀ i, right < A i * n + 1) (hs : ∀ i, s < A i * n + 1) (hh : 1 ≤ height) :
    hankelIntegral right height (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x) =
      hankelIntegral s height (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x) := by
  have hrect := Analytic.rectangle_integral_identity (differentiableOn_weighted_kernel r b A z j n k)
    (a := right) (r := s) (A := -height) (B := height)
    (fun x hx _ => ⟨Complex.mem_slitPlane_iff.mpr (Or.inl ((lt_min hright0 hs0).trans_le hx.1)),
      fun i => hx.2.trans_lt (max_lt_iff.mpr ⟨hright i, hs i⟩)⟩)
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hrect
  have hiR := weighted_hankel_absolutely_convergent hr hA b z j n k hright0 hright hh
  have hiS := weighted_hankel_absolutely_convergent hr hA b z j n k hs0 hs hh
  have hlo := intervalIntegral.integral_Iic_sub_Iic hiR.1 hiS.1
  have hhi := intervalIntegral.integral_Iic_sub_Iic hiR.2.2 hiS.2.2
  dsimp only [hankelIntegral]
  linear_combination -hrect - hlo + hhi

theorem branchIntegral_eq_deformed {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) (k : Fin r)
    {right height : ℝ} (hright0 : 0 < right) (hright : ∀ i, right < A i * n + 1) (hh : 1 ≤ height) :
    branchIntegral r b A z j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      hankelIntegral right height (fun x => ((b : ℂ) * n - x) ^ k.val * kernel r b A z j n x) := by
  have href (i : Fin (r - 1)) : (1 / 2 : ℝ) < A i * n + 1 := by
    nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n]
  exact congrArg (fun w : ℂ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * w)
    ((weighted_hankel_height_eq hr hA b z j n k.val (by norm_num) href le_rfl hh).trans
      (weighted_hankel_right_eq hr hA b z j n k.val (by norm_num) hright0 href hright hh))

end ThisWork.HigherRank
