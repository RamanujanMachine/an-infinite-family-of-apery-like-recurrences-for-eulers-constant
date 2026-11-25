module

public import ThisWork.GrowthRates
public import ThisWork.CenterNormComparison

/-! The exact polynomial change of center transfers every proved branch
rate, including the even-rank boundary rate. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

theorem HasLogNormGrowth.recenter_branch {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    {j : ℤ} {a : ℝ} (hv : HasLogNormGrowth r (commonScale r 0 A z) a (branchIntegral r 0 A z j))
    (b : ℕ) :
    HasLogNormGrowth r (commonScale r b A z) a (branchIntegral r b A z j) := by
  obtain ⟨C, hC, hb⟩ := hv
  let Q := (r - 1 : ℕ) * (Real.log (1 + (b : ℝ)) + 1)
  have hm : 0 ≤ Real.log (1 + (b : ℝ)) := Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg b))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨C + Q * (2 * ((r : ℝ) + 1)), by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  obtain ⟨hIm, hchange⟩ := logNorm_branchIntegral_recenter (by omega : 0 < r) hA b z j hn1 hn.1
  refine ⟨hIm, ?_⟩
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hpol : (r - 1 : ℕ) * (Real.log (1 + (b : ℝ)) + Real.log (n : ℝ)) ≤
      Q * (1 + Real.log (n : ℝ)) := by
    dsimp only [Q]
    nlinarith [mul_nonneg hm hlogn, Nat.cast_nonneg (α := ℝ) (r - 1),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) (r - 1)) (mul_nonneg hm hlogn)]
  have hsmall := (hchange.trans hpol).trans
    (mul_le_mul_of_nonneg_left (one_add_log_nat_le_errorScale hr hn1) hQ)
  rw [log_commonScale_center hA hz]
  have hab := abs_add_le
    (Real.log ‖branchIntegral r 0 A z j n‖ - Real.log (commonScale r 0 A z n) - a * largeScale r n)
    (Real.log ‖branchIntegral r b A z j n‖ - Real.log ‖branchIntegral r 0 A z j n‖ -
      Real.log z * ((b : ℝ) * n))
  have hid (x y z t u : ℝ) : (x - z - t) + (y - x - u) = y - (z + u) - t := by ring
  rw [hid] at hab
  nlinarith [hn.2]

end ThisWork
