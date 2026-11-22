module

public import ThisWork.HigherRank.BoundaryCompactBounds
public import ThisWork.HigherRank.ReflectedIntegralLower
public import ThisWork.HigherRank.ReflectedIntegralUpper

/-! The actual boundary Hankel integral differs from the positive real
integral by two small infinite-bank errors and fixed finite pieces. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem integrableOn_boundaryKernel_horizontal {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (m : ℕ) (z : ℝ) (n : ℕ) {right y : ℝ} (hright : right < 1) (hy : |y| = 1) :
    IntegrableOn (fun u : ℝ => boundaryKernel r m A z n ((u : ℂ) + (y : ℂ) * Complex.I)) (Iic right) := by
  apply Analytic.integrableOn_Iic_of_exp_bound
  · intro u hu
    have hs : (u : ℂ) + (y : ℂ) * Complex.I ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (by
        have hy0 : y ≠ 0 := by intro he; simp [he] at hy
        simpa using hy0))
    have hd := differentiableAt_boundaryKernel_of_slit hA m z n hs
      (by simpa [Complex.mul_re] using hu.trans_lt hright)
    exact (hd.continuousAt.comp (f := fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop)).continuousWithinAt
  have h := tendsto_neg_atBot_atTop.eventually
    (uniform_weighted_boundary_left_decay hr hA (H := 1) le_rfl half hrh m z n 0 1)
  exact h.mono (fun u hu => by simpa using hu y hy.ge hy.le)

noncomputable def boundaryFixedCorrection (r m : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (n : ℕ) (L : ℝ) : ℂ :=
  (∫ u in L..(1 / 2 : ℝ), boundaryKernel r m A z n ((u : ℂ) - Complex.I)) -
    (∫ u in L..(1 / 2 : ℝ), boundaryKernel r m A z n ((u : ℂ) + Complex.I)) +
    (∫ y in (-1 : ℝ)..1, Complex.I * boundaryKernel r m A z n ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)) -
    2 * (Real.pi : ℂ) * Complex.I *
      (∫ y in (-1 : ℝ)..0, Complex.I * reflectedKernel r m A z n ((L : ℂ) + (y : ℂ) * Complex.I))

theorem boundary_hankel_error_identity {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (m : ℕ) (z : ℝ) (n : ℕ) {L : ℝ} (hL : L < 1) :
    hankelIntegral (1 / 2) 1 (boundaryKernel r m A z n) -
        2 * (Real.pi : ℂ) * Complex.I * (reflectedRealIntegral r m A z n L : ℂ) =
      (∫ u in Iic L, boundaryKernel r m A z n ((u : ℂ) - Complex.I) -
        2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r m A z n ((u : ℂ) - Complex.I)) -
      (∫ u in Iic L, boundaryKernel r m A z n ((u : ℂ) + Complex.I)) +
        boundaryFixedCorrection r m A z n L := by
  have himinus (a : ℝ) (ha : a < 1) :
      IntegrableOn (fun u : ℝ => boundaryKernel r m A z n ((u : ℂ) - Complex.I)) (Iic a) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] using
      integrableOn_boundaryKernel_horizontal hr hA half hrh m z n ha (y := -1) (by norm_num)
  have hiplus (a : ℝ) (ha : a < 1) :=
    integrableOn_boundaryKernel_horizontal hr hA half hrh m z n ha (y := 1) (by norm_num)
  have hlo := intervalIntegral.integral_Iic_sub_Iic (himinus L hL) (himinus (1 / 2) (by norm_num))
  have hhi := intervalIntegral.integral_Iic_sub_Iic (hiplus L hL) (hiplus (1 / 2) (by norm_num))
  have hq : IntegrableOn (fun u : ℝ => reflectedKernel r m A z n ((u : ℂ) - Complex.I)) (Iic L) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] using
      integrableOn_reflectedKernel_horizontal hr hA half hrh m z n hL (y := -1) (by norm_num)
  have hsub := integral_sub (himinus L hL) (hq.const_mul (2 * (Real.pi : ℂ) * Complex.I))
  rw [integral_const_mul] at hsub
  have hbank := reflected_lower_bank_eq_real hr hA half hrh m z n hL
  rw [reflected_integral_eq_positive hA m z n hL] at hbank
  simp only [Complex.ofReal_one, one_mul] at hhi
  dsimp only [hankelIntegral, boundaryFixedCorrection]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, one_mul]
  linear_combination hlo - hhi - hsub + 2 * (Real.pi : ℂ) * Complex.I * hbank

theorem boundary_hankel_error_le {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (m : ℕ) (z : ℝ) (n : ℕ) {L : ℝ} (hL : L ≤ -(6 * (r : ℝ))) :
    ‖hankelIntegral (1 / 2) 1 (boundaryKernel r m A z n) -
        2 * (Real.pi : ℂ) * Complex.I * (reflectedRealIntegral r m A z n L : ℂ)‖ ≤
      (Real.pi / 2) * reflectedRealIntegral r m A z n L + ‖boundaryFixedCorrection r m A z n L‖ := by
  have hL1 : L < 1 := by have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr; linarith
  have himinus : IntegrableOn (fun u : ℝ => boundaryKernel r m A z n ((u : ℂ) - Complex.I)) (Iic L) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] using
      integrableOn_boundaryKernel_horizontal hr hA half hrh m z n hL1 (y := -1) (by norm_num)
  have hiplus : IntegrableOn (fun u : ℝ => boundaryKernel r m A z n ((u : ℂ) + Complex.I)) (Iic L) := by
    simpa only [Complex.ofReal_one, one_mul] using
      integrableOn_boundaryKernel_horizontal hr hA half hrh m z n hL1 (y := 1) (by norm_num)
  have hq : IntegrableOn (fun u : ℝ => reflectedKernel r m A z n ((u : ℂ) - Complex.I)) (Iic L) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] using
      integrableOn_reflectedKernel_horizontal hr hA half hrh m z n hL1 (y := -1) (by norm_num)
  have hreal : IntegrableOn (fun u : ℝ => ‖reflectedKernel r m A z n (u : ℂ)‖) (Iic L) := by
    change Integrable _ _
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      (integrableOn_reflectedKernel_horizontal hr hA half hrh m z n hL1 (y := 0) (by norm_num)).norm
  have hbound {f : ℝ → ℂ} (hf : IntegrableOn f (Iic L))
      (hb : ∀ x ≤ L, ‖f x‖ ≤ (Real.pi / 4) * ‖reflectedKernel r m A z n (x : ℂ)‖) :
      ‖∫ x in Iic L, f x‖ ≤ (Real.pi / 4) * reflectedRealIntegral r m A z n L := by
    calc
      _ ≤ ∫ x in Iic L, ‖f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Iic L, (Real.pi / 4) * ‖reflectedKernel r m A z n (x : ℂ)‖ :=
        setIntegral_mono_on hf.norm (hreal.const_mul _) measurableSet_Iic hb
      _ = _ := integral_const_mul _ _
  have hp := hbound hiplus (fun x hx => (fixed_boundary_bank_errors_le hr hA m z n (hx.trans hL)).1)
  have hm := hbound (himinus.sub (hq.const_mul (2 * (Real.pi : ℂ) * Complex.I)))
    (fun x hx => (fixed_boundary_bank_errors_le hr hA m z n (hx.trans hL)).2)
  simp only [Pi.sub_apply] at hm
  rw [boundary_hankel_error_identity hr hA half hrh m z n hL1]
  have ht := norm_sub_le
    (∫ u in Iic L, boundaryKernel r m A z n ((u : ℂ) - Complex.I) -
      2 * (Real.pi : ℂ) * Complex.I * reflectedKernel r m A z n ((u : ℂ) - Complex.I))
    (∫ u in Iic L, boundaryKernel r m A z n ((u : ℂ) + Complex.I))
  exact (norm_add_le _ _).trans (by linarith)

end ThisWork.HigherRank
