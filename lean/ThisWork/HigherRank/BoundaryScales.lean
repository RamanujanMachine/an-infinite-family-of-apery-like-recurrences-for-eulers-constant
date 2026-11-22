module

public import ThisWork.HigherRank.Scales

/-! Elementary absorption of polynomial factors at the error scale of
the arbitrary-rank asymptotic estimates. -/

@[expose] public section
namespace ThisWork.HigherRank

open Filter
open scoped Topology

theorem one_le_errorScale {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n) :
    1 ≤ largeScale r n * smallParameter r n := by
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  simpa only [mul_comm] using (div_le_iff₀ hR).mp (inv_largeScale_le_smallParameter hr hn)

theorem one_add_log_nat_le_errorScale {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n) :
    1 + Real.log (n : ℝ) ≤ (2 * ((r : ℝ) + 1)) * (largeScale r n * smallParameter r n) := by
  have hl := log_largeScale (show 0 < r by omega) (show 0 < n by omega)
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hR : 1 ≤ largeScale r n := Real.one_le_rpow (by exact_mod_cast hn)
    (sub_nonneg.mpr ((div_le_one (by linarith : (0 : ℝ) < r)).mpr (by linarith)))
  have hlogR := Real.log_nonneg hR
  have htwo : Real.log (n : ℝ) ≤ 2 * Real.log (largeScale r n) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (r : ℝ) - 2) hln]
  nlinarith [one_add_log_largeScale_le hr hn]

theorem polynomial_le_exp_errorScale {r n : ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    B * Real.exp (C * (1 + Real.log (n : ℝ))) ≤
      Real.exp ((B + C * (2 * ((r : ℝ) + 1))) * (largeScale r n * smallParameter r n)) := by
  have he : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  calc
    _ ≤ Real.exp B * Real.exp (C * (1 + Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp (B + C * (1 + Real.log (n : ℝ))) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left (one_add_log_nat_le_errorScale hr hn) hC,
        mul_le_mul_of_nonneg_left (one_le_errorScale hr hn) hB])

theorem eventually_exp_errorScale_le {r : ℕ} (hr : 0 < r) {a : ℝ} (ha : 0 < a)
    (C D : ℝ) : ∀ᶠ n : ℕ in atTop,
    Real.exp (C * (largeScale r n * smallParameter r n)) ≤
      Real.exp (a * largeScale r n - D * (largeScale r n * smallParameter r n)) := by
  have ht := (smallParameter_tendsto hr).const_mul (C + D)
  have hb : ∀ᶠ n : ℕ in atTop, (C + D) * smallParameter r n < a :=
    ht.eventually (gt_mem_nhds (by simpa using ha))
  filter_upwards [hb] with n hn
  apply Real.exp_le_exp.mpr
  have hR : 0 ≤ largeScale r n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  nlinarith [mul_le_mul_of_nonneg_left hn.le hR]

end ThisWork.HigherRank
