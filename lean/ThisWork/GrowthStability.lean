module

public import ThisWork.GrowthRates

/-! Stability of a logarithmic growth rate under bounded conditioning and
strictly smaller perturbations. -/

@[expose] public section
namespace ThisWork

open Filter Asymptotics
open scoped Topology

theorem HasLogNormGrowth.of_norm_comparison
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    {r : ℕ} (hr : 3 ≤ r) {s : ℕ → ℝ} {a : ℝ} {v : ℕ → V} {w : ℕ → W}
    (hv : HasLogNormGrowth r s a v) {L U : ℝ} (hL : 0 < L) (hU : 0 < U)
    (hcomp : ∀ᶠ n : ℕ in atTop, ‖v n‖ ≤ L * ‖w n‖ ∧ ‖w n‖ ≤ U * ‖v n‖) :
    HasLogNormGrowth r s a w := by
  obtain ⟨C, hC, hb⟩ := hv
  refine ⟨C + |Real.log L| + |Real.log U|, by positivity, ?_⟩
  filter_upwards [hb, hcomp, eventually_ge_atTop (1 : ℕ)] with n hn hc hn1
  have hw : 0 < ‖w n‖ := by
    by_contra! hw
    exact (not_le_of_gt hn.1) (hc.1.trans (mul_nonpos_of_nonneg_of_nonpos hL.le hw))
  refine ⟨hw, ?_⟩
  have hlo := Real.log_le_log hn.1 hc.1
  have hup := Real.log_le_log hw hc.2
  rw [Real.log_mul hL.ne' hw.ne'] at hlo
  rw [Real.log_mul hU.ne' hn.1.ne'] at hup
  have hd : |Real.log ‖w n‖ - Real.log ‖v n‖| ≤ |Real.log L| + |Real.log U| :=
    abs_le.mpr ⟨by linarith [le_abs_self (Real.log L), abs_nonneg (Real.log U)],
      by linarith [le_abs_self (Real.log U), abs_nonneg (Real.log L)]⟩
  have ht := abs_add_le (Real.log ‖w n‖ - Real.log ‖v n‖)
    (Real.log ‖v n‖ - Real.log (s n) - a * largeScale r n)
  have hid (x y z t : ℝ) : (x - y) + (y - z - t) = x - z - t := by ring
  rw [hid] at ht
  have he := one_le_errorScale hr hn1
  nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (Real.log L)),
    mul_le_mul_of_nonneg_left he (abs_nonneg (Real.log U)), hn.2]

theorem HasLogNormGrowth.add_smaller
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {r : ℕ} (hr : 3 ≤ r) {s : ℕ → ℝ} {a : ℝ} {v u : ℕ → V}
    (hv : HasLogNormGrowth r s a v) (hu : u =o[atTop] v) {c : ℂ} (hc : c ≠ 0) :
    HasLogNormGrowth r s a (fun n => c • v n + u n) := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  apply hv.of_norm_comparison hr (L := (‖c‖ / 2)⁻¹) (U := 2 * ‖c‖)
    (by positivity) (by positivity)
  filter_upwards [hu.bound (show 0 < ‖c‖ / 2 by positivity)] with n hn
  have hlo := norm_sub_le (c • v n + u n) (u n)
  rw [add_sub_cancel_right, norm_smul] at hlo
  have hup := norm_add_le (c • v n) (u n)
  rw [norm_smul] at hup
  have hl : (‖c‖ / 2) * ‖v n‖ ≤ ‖c • v n + u n‖ := by linarith
  constructor
  · have h := (le_div_iff₀ (show 0 < ‖c‖ / 2 by positivity)).mpr (by simpa only [mul_comm] using hl)
    simpa only [div_eq_mul_inv, mul_comm] using h
  · nlinarith [norm_nonneg (v n)]

end ThisWork
