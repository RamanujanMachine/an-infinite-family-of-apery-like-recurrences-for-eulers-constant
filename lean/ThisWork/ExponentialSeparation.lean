module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The rank-three exponential gap absorbs every fixed polynomial. -/

@[expose] public section
namespace ThisWork.Analytic

open Filter
open scoped Topology

theorem tendsto_nat_pow_mul_exp_gap {a : ℝ} (ha : 0 < a) (b : ℝ) (N : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ N * Real.exp
      (-a * (n : ℝ) ^ (2 / 3 : ℝ) + b * (n : ℝ) ^ (1 / 3 : ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3 * (N : ℝ)) 1 zero_lt_one).comp ht
  have hlim' : Tendsto (fun n : ℕ => (n : ℝ) ^ N * Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    convert hlim using 1
    funext n
    dsimp only [Function.comp_apply]
    rw [← Real.rpow_mul (Nat.cast_nonneg n), show (1 / 3 : ℝ) * (3 * (N : ℝ)) = N by ring,
      Real.rpow_natCast, neg_one_mul]
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ hlim'
  filter_upwards [ht.eventually (eventually_ge_atTop ((b + 1) / a))] with n hn
  have he : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hid : (n : ℝ) ^ (2 / 3 : ℝ) = ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
  have hb := (div_le_iff₀ ha).mp hn
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (pow_nonneg (Nat.cast_nonneg n) N)
  rw [hid]
  nlinarith [mul_nonneg he (show 0 ≤ a * (n : ℝ) ^ (1 / 3 : ℝ) - (b + 1) by linarith)]

end ThisWork.Analytic
