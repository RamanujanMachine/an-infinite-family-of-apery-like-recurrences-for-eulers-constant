module

public import ThisWork.GrowthRates

/-! A polynomial coefficient lower bound upgrades individual rate separation
to separation from a fixed nontrivial combination. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

theorem separation_of_coefficient_bound
    {V W U : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup U]
    {r : ℕ} (hr : 1 < r) {s : ℕ → ℝ} {a b : ℝ}
    {v : ℕ → V} {w : ℕ → W} {u : ℕ → U}
    (hv : HasLogNormGrowth r s a v) (hu : HasLogNormGrowth r s b u) (hab : a < b)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (p : ℕ)
    (hb : ∀ᶠ n : ℕ in atTop, c * ‖u n‖ ≤ K * (n : ℝ) ^ p * ‖w n‖) :
    (∀ᶠ n : ℕ in atTop, w n ≠ 0) ∧
      ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N * (‖v n‖ / ‖w n‖)) atTop (𝓝 0) := by
  have hw : ∀ᶠ n : ℕ in atTop, 0 < ‖w n‖ := by
    filter_upwards [hb, hu.choose_spec.2] with n hn hnU
    by_contra! hzero
    have hp : 0 ≤ K * (n : ℝ) ^ p := by positivity
    have hh := mul_nonpos_of_nonneg_of_nonpos hp hzero
    exact (not_le_of_gt (mul_pos hc hnU.1)) (hn.trans hh)
  refine ⟨hw.mono (fun _ hn => norm_pos_iff.mp hn), fun N => ?_⟩
  have hlim := (hv.superpolynomial_separation hr hu hab (N + p)).const_mul (K / c)
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _
    (by simpa only [mul_zero] using hlim)
  filter_upwards [hb, hw, hu.choose_spec.2] with n hn hnW hnU
  have hratio : ‖v n‖ / ‖w n‖ ≤ (K / c) * (n : ℝ) ^ p * (‖v n‖ / ‖u n‖) := by
    rw [show (K / c) * (n : ℝ) ^ p = K * (n : ℝ) ^ p / c by ring,
      div_mul_div_comm]
    apply (div_le_div_iff₀ hnW (mul_pos hc hnU.1)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (v n))]
  calc
    _ ≤ (n : ℝ) ^ N * ((K / c) * (n : ℝ) ^ p * (‖v n‖ / ‖u n‖)) :=
      mul_le_mul_of_nonneg_left hratio (pow_nonneg (Nat.cast_nonneg n) N)
    _ = _ := by rw [pow_add]; ring

end ThisWork
