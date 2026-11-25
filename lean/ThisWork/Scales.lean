module

public import ThisWork.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The small parameter and the saddle scale in arbitrary rank. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

noncomputable def smallParameter (r n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / (r : ℝ)))

noncomputable def largeScale (r n : ℕ) : ℝ := (n : ℝ) ^ (1 - 1 / (r : ℝ))

theorem saddleScale_pos {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) : 0 < saddleScale r A z := by
  apply Real.rpow_pos_of_pos
  exact mul_pos (Finset.prod_pos (fun i _ => hA i)) hz

theorem saddleScale_pow {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    saddleScale r A z ^ r = (∏ i, A i) * z := by
  simpa only [saddleScale, one_div] using
    Real.rpow_inv_natCast_pow (mul_pos (Finset.prod_pos (fun i _ => hA i)) hz).le hr.ne'

theorem log_saddleScale {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) :
    (r : ℝ) * Real.log (saddleScale r A z) = (∑ i, Real.log (A i)) + Real.log z := by
  have h := congrArg Real.log (saddleScale_pow hr hA hz)
  rw [Real.log_pow, Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => (hA i).ne')) hz.ne',
    Real.log_prod (fun i _ => (hA i).ne')] at h
  exact h

theorem smallParameter_tendsto {r : ℕ} (hr : 0 < r) :
    Tendsto (smallParameter r) atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (div_pos zero_lt_one (Nat.cast_pos.mpr hr))).comp
    tendsto_natCast_atTop_atTop

theorem largeScale_tendsto {r : ℕ} (hr : 1 < r) :
    Tendsto (largeScale r) atTop atTop := by
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have he : 0 < 1 - 1 / (r : ℝ) :=
    sub_pos.mpr ((div_lt_one (lt_trans zero_lt_one hrR)).mpr hrR)
  exact (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop

theorem largeScale_div_nat (r : ℕ) {n : ℕ} (hn : 0 < n) :
    largeScale r n / (n : ℝ) = smallParameter r n := by
  rw [smallParameter, show -(1 / (r : ℝ)) = (1 - 1 / (r : ℝ)) - 1 by ring,
    Real.rpow_sub_one (Nat.cast_ne_zero.mpr hn.ne')]
  rfl

theorem largeScale_div_nat_tendsto {r : ℕ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => largeScale r n / (n : ℝ)) atTop (𝓝 0) := by
  apply (smallParameter_tendsto hr).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (largeScale_div_nat r hn).symm

theorem largeScale_pow {r : ℕ} (hr : 0 < r) (n : ℕ) :
    largeScale r n ^ r = (n : ℝ) ^ (r - 1) := by
  rw [largeScale, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
    ← Real.rpow_natCast]
  congr 1
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr.ne'), Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr hr.ne']

theorem largeScale_mul_smallParameter_sq (r : ℕ) {n : ℕ} (hn : 0 < n) :
    largeScale r n * smallParameter r n ^ 2 = (n : ℝ) ^ (1 - 3 / (r : ℝ)) := by
  rw [largeScale, smallParameter, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  norm_num
  ring

theorem one_le_largeScale_mul_smallParameter_sq {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n) :
    1 ≤ largeScale r n * smallParameter r n ^ 2 := by
  rw [largeScale_mul_smallParameter_sq r (by omega)]
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  exact Real.one_le_rpow (by exact_mod_cast hn)
    (sub_nonneg.mpr ((div_le_one hr0).mpr hrR))

theorem smallParameter_le_one (r : ℕ) {n : ℕ} (hn : 1 ≤ n) : smallParameter r n ≤ 1 := by
  simpa only [smallParameter, Real.rpow_zero] using
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n)
      (neg_nonpos.mpr (div_nonneg zero_le_one (Nat.cast_nonneg r)))

theorem inv_largeScale_le_smallParameter {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n) :
    1 / largeScale r n ≤ smallParameter r n := by
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have he : 0 < smallParameter r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  apply (div_le_iff₀ hR).mpr
  have hs : smallParameter r n ^ 2 ≤ smallParameter r n := by
    nlinarith [smallParameter_le_one r hn]
  simpa only [mul_comm] using
    (one_le_largeScale_mul_smallParameter_sq hr hn).trans (mul_le_mul_of_nonneg_left hs hR.le)

theorem log_largeScale {r : ℕ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    (r : ℝ) * Real.log (largeScale r n) = ((r : ℝ) - 1) * Real.log (n : ℝ) := by
  rw [largeScale, Real.log_rpow (Nat.cast_pos.mpr hn)]
  field_simp [Nat.cast_ne_zero.mpr hr.ne']

theorem inv_nat_le_smallParameter {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ smallParameter r n := by
  rw [smallParameter, one_div, ← Real.rpow_neg_one]
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hdiv : 1 / (r : ℝ) ≤ 1 :=
    (div_le_one (lt_of_lt_of_le zero_lt_one hrR)).mpr hrR
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem largeScale_mul_smallParameter (r : ℕ) {n : ℕ} (hn : 0 < n) :
    largeScale r n * smallParameter r n = (n : ℝ) ^ (1 - 2 / (r : ℝ)) := by
  rw [largeScale, smallParameter, ← Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem one_add_log_largeScale_le {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n) :
    1 + Real.log (largeScale r n) ≤ ((r : ℝ) + 1) * (largeScale r n * smallParameter r n) := by
  have hr0 : 0 < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have hRn : largeScale r n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le hn1
    (by linarith [div_nonneg zero_le_one hr0.le] : 1 - 1 / (r : ℝ) ≤ 1)
  have hexp : 1 / (r : ℝ) ≤ 1 - 2 / (r : ℝ) := by
    rw [le_sub_iff_add_le, ← add_div]
    norm_num
    exact (div_le_one hr0).mpr (show (3 : ℝ) ≤ r by exact_mod_cast hr)
  have hpow : (n : ℝ) ^ (1 / (r : ℝ)) ≤ largeScale r n * smallParameter r n := by
    rw [largeScale_mul_smallParameter r (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg n) (div_pos zero_lt_one hr0)
  have hdiv : (n : ℝ) ^ (1 / (r : ℝ)) / (1 / (r : ℝ)) = (r : ℝ) * (n : ℝ) ^ (1 / (r : ℝ)) := by field_simp
  rw [hdiv] at hlog
  have hone : 1 ≤ largeScale r n * smallParameter r n :=
    (div_le_iff₀ hR).mp (inv_largeScale_le_smallParameter hr hn) |>.trans_eq (mul_comm _ _)
  nlinarith [Real.log_le_log hR hRn, mul_le_mul_of_nonneg_left hpow hr0.le]

end ThisWork
