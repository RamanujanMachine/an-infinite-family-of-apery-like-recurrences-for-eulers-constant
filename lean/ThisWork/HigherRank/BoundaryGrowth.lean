module

public import ThisWork.HigherRank.FixedContourGrowth

/-! Growth of the actual even-rank boundary Hankel integral, with symbolic
positive argument. The proof compares it with a positive real integral. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem FixedPolynomialBound.eventually_le_reflectedRealIntegral {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z right q : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (hright : right < 1) (b : ℕ) (hq : 0 < q)
    {f : ℕ → ℂ} (hf : FixedPolynomialBound (commonScale r b A z) f) :
    ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ q * reflectedRealIntegral r b A z n right := by
  obtain ⟨B, hB, C, hC, hb⟩ := hf
  obtain ⟨D, _, hlower⟩ := reflectedRealIntegral_lower hr hA hz half hrh hright b
  let F := B + C * (2 * ((r : ℝ) + 1))
  have ha : 0 < (r : ℝ) * saddleScale r A z := mul_pos (Nat.cast_pos.mpr (by omega)) (saddleScale_pos hA hz)
  filter_upwards [hb, hlower, eventually_exp_errorScale_le (show 0 < r by omega) ha (F + |Real.log q|) D,
    eventually_ge_atTop (1 : ℕ)] with n hn hnL hnE hn1
  let E := largeScale r n * smallParameter r n
  have hcs := (commonScale_pos hA hz b n).le
  have hpoly := polynomial_le_exp_errorScale hr hn1 hB hC
  have he : 1 ≤ E := one_le_errorScale hr hn1
  have hqexp : Real.exp (F * E) ≤ q * Real.exp ((F + |Real.log q|) * E) := by
    calc
      _ ≤ Real.exp (Real.log q + (F + |Real.log q|) * E) :=
        Real.exp_le_exp.mpr (by nlinarith [neg_le_abs (Real.log q),
          (mul_le_mul_of_nonneg_left he (abs_nonneg (Real.log q)))])
      _ = _ := by rw [Real.exp_add, Real.exp_log hq]
  calc
    _ ≤ B * commonScale r b A z n * Real.exp (C * (1 + Real.log (n : ℝ))) := hn
    _ = commonScale r b A z n * (B * Real.exp (C * (1 + Real.log (n : ℝ)))) := by ring
    _ ≤ commonScale r b A z n * Real.exp (F * E) := mul_le_mul_of_nonneg_left hpoly hcs
    _ ≤ commonScale r b A z n * (q * Real.exp ((F + |Real.log q|) * E)) := mul_le_mul_of_nonneg_left hqexp hcs
    _ ≤ commonScale r b A z n * (q * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n - D * E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnE hq.le) hcs
    _ = q * (commonScale r b A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n - D * E)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnL hq.le

theorem boundary_hankel_comparable_real {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (b : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Real.pi * reflectedRealIntegral r b A z n (-(6 * (r : ℝ))) ≤
        ‖hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)‖ ∧
      ‖hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)‖ ≤
        3 * Real.pi * reflectedRealIntegral r b A z n (-(6 * (r : ℝ))) := by
  let L := -(6 * (r : ℝ))
  have hL : L < 1 := by have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); dsimp only [L]; linarith
  have hp := boundaryFixedCorrection_polynomial_bound (by omega : 0 < r) hA hz b
    (show L ≤ 1 / 2 by dsimp only [L]; have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); linarith)
  filter_upwards [hp.eventually_le_reflectedRealIntegral hr hA hz half hrh hL b
    (show 0 < Real.pi / 2 by positivity)] with n hn
  let J := reflectedRealIntegral r b A z n L
  let H := hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)
  let v := 2 * (Real.pi : ℂ) * Complex.I * (J : ℂ)
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  have he : ‖H - v‖ ≤ Real.pi * J := by
    have h := boundary_hankel_error_le (by omega : 0 < r) hA half hrh b z n (L := L) le_rfl
    change ‖H - v‖ ≤ _ at h
    nlinarith
  have hv : ‖v‖ = 2 * Real.pi * J := by
    simp only [v, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_of_nonneg hJ]
  have hlo := norm_sub_norm_le v H
  rw [norm_sub_rev] at hlo
  have hupper := norm_add_le (H - v) v
  rw [sub_add_cancel] at hupper
  exact ⟨by nlinarith [he, hv], by nlinarith [he, hv]⟩

theorem boundary_hankel_growth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)‖ -
        Real.log (commonScale r b A z n) - (r : ℝ) * saddleScale r A z * largeScale r n| ≤
          C * (largeScale r n * smallParameter r n) := by
  let L := -(6 * (r : ℝ))
  have hL : L < 1 := by have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); dsimp only [L]; linarith
  obtain ⟨D, hD, hlower⟩ := reflectedRealIntegral_lower hr hA hz half hrh hL b
  obtain ⟨E, hE, hupper⟩ := reflectedRealIntegral_upper hr hA hz half hrh hL b
  refine ⟨D + E + 3 * Real.pi, by positivity, ?_⟩
  filter_upwards [hlower, hupper, boundary_hankel_comparable_real hr hA hz half hrh b,
    eventually_ge_atTop (1 : ℕ)] with n hnL hnU hnH hn1
  let R := largeScale r n
  let e := smallParameter r n
  let a := (r : ℝ) * saddleScale r A z * R
  let S := commonScale r b A z n
  let H := hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)
  have hS : 0 < S := commonScale_pos hA hz b n
  have he : 1 ≤ R * e := one_le_errorScale hr hn1
  have hlo : S * Real.exp (a - D * (R * e)) ≤ ‖H‖ := by
    have hJ : 0 ≤ reflectedRealIntegral r b A z n L := integral_nonneg (fun _ => norm_nonneg _)
    nlinarith [hnH.1, Real.pi_gt_three]
  have hH : 0 < ‖H‖ := (mul_pos hS (Real.exp_pos _)).trans_le hlo
  have hup : ‖H‖ ≤ S * Real.exp (a + (E + 3 * Real.pi) * (R * e)) := by
    have hc : 3 * Real.pi ≤ Real.exp (3 * Real.pi * (R * e)) := by
      have h := Real.add_one_le_exp (3 * Real.pi * (R * e))
      nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 3 * Real.pi by positivity)]
    calc
      _ ≤ 3 * Real.pi * reflectedRealIntegral r b A z n L := hnH.2
      _ ≤ 3 * Real.pi * (S * Real.exp (a + E * (R * e))) :=
        mul_le_mul_of_nonneg_left hnU (by positivity)
      _ ≤ Real.exp (3 * Real.pi * (R * e)) * (S * Real.exp (a + E * (R * e))) :=
        mul_le_mul_of_nonneg_right hc (mul_pos hS (Real.exp_pos _)).le
      _ = _ := by rw [mul_left_comm, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hl := Real.log_le_log (mul_pos hS (Real.exp_pos _)) hlo
  have hu := Real.log_le_log hH hup
  rw [Real.log_mul hS.ne' (Real.exp_ne_zero _), Real.log_exp] at hl hu
  change |Real.log ‖H‖ - Real.log S - a| ≤ _
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg (add_nonneg hE (by positivity : 0 ≤ 3 * Real.pi)) (by linarith : 0 ≤ R * e)],
    by nlinarith [mul_nonneg hD (by linarith : 0 ≤ R * e)]⟩

theorem eventually_boundary_hankel_ne_zero {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n) ≠ 0 := by
  have hL : -(6 * (r : ℝ)) < 1 := by have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); linarith
  obtain ⟨C, _, hb⟩ := reflectedRealIntegral_lower hr hA hz half hrh hL b
  filter_upwards [hb, boundary_hankel_comparable_real hr hA hz half hrh b] with n hn hc
  have hJ := (mul_pos (commonScale_pos hA hz b n) (Real.exp_pos _)).trans_le hn
  exact norm_pos_iff.mp ((mul_pos Real.pi_pos hJ).trans_le hc.1)

/-- The normalized boundary integral has the full leading exponential rate,
with the same `n^(1-2/r)` error as the off-cut saddle estimates. -/
theorem boundary_integral_growth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)‖ -
        Real.log (commonScale r b A z n) - (r : ℝ) * saddleScale r A z * largeScale r n| ≤
          C * (largeScale r n * smallParameter r n) := by
  let w : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  have hw : w ≠ 0 := inv_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  obtain ⟨C, hC, hb⟩ := boundary_hankel_growth hr hA hz half hrh b
  refine ⟨C + |Real.log ‖w‖|, by positivity, ?_⟩
  filter_upwards [hb, eventually_boundary_hankel_ne_zero hr hA hz half hrh b,
    eventually_ge_atTop (1 : ℕ)] with n hn hH hn1
  change |Real.log ‖w * _‖ - _ - _| ≤ _
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hw) (norm_ne_zero_iff.mpr hH)]
  have ht := abs_add_le (Real.log ‖w‖)
    (Real.log ‖hankelIntegral (1 / 2) 1 (boundaryKernel r b A z n)‖ -
      Real.log (commonScale r b A z n) - (r : ℝ) * saddleScale r A z * largeScale r n)
  have he := mul_le_mul_of_nonneg_left (one_le_errorScale hr hn1) (abs_nonneg (Real.log ‖w‖))
  have hid (a auxB c d : ℝ) : a + auxB - c - d = a + (auxB - c - d) := by ring
  rw [hid]
  nlinarith

end ThisWork.HigherRank
