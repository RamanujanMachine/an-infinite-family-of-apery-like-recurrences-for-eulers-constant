module

public import ThisWork.BoundaryScales
public import Mathlib.Analysis.Asymptotics.Lemmas

/-! Exponential growth comparisons at the common arbitrary-rank scale. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

def HasLogNormGrowth {V : Type*} [NormedAddCommGroup V]
    (r : ℕ) (scale : ℕ → ℝ) (rate : ℝ) (v : ℕ → V) : Prop :=
  ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, 0 < ‖v n‖ ∧
    |Real.log ‖v n‖ - Real.log (scale n) - rate * largeScale r n| ≤
      C * (largeScale r n * smallParameter r n)

/-- Convert logarithmic norm control into the corresponding exponential estimate. -/
theorem HasLogNormGrowth.normEstimate {V : Type*} [NormedAddCommGroup V]
    {r : ℕ} {scale : ℕ → ℝ} {rate : ℝ} {v : ℕ → V}
    (hv : HasLogNormGrowth r scale rate v) (hs : ∀ n, 0 < scale n) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ E : ℝ,
      |E| ≤ C * (n : ℝ) ^ (1 - 2 / (r : ℝ)) ∧
      ‖v n‖ = scale n * Real.exp (rate * largeScale r n + E) := by
  obtain ⟨C, hC, hb⟩ := hv
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  let E := Real.log ‖v n‖ - Real.log (scale n) - rate * largeScale r n
  refine ⟨E, ?_, ?_⟩
  · simpa only [largeScale_mul_smallParameter r hn0] using hn.2
  · calc
      ‖v n‖ = Real.exp (Real.log ‖v n‖) := (Real.exp_log hn.1).symm
      _ = Real.exp (Real.log (scale n) + (rate * largeScale r n + E)) := by
        congr 1
        dsimp only [E]
        ring
      _ = _ := by rw [Real.exp_add, Real.exp_log (hs n)]

theorem tendsto_nat_pow_mul_exp_gap {r : ℕ} (hr : 1 < r) {a : ℝ}
    (ha : 0 < a) (b : ℝ) (N : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ N * Real.exp
      (-a * largeScale r n + b * (largeScale r n * smallParameter r n))) atTop (𝓝 0) := by
  let p := 1 - 1 / (r : ℝ)
  have hp : 0 < p := by
    have hrR : (1 : ℝ) < r := by exact_mod_cast hr
    dsimp only [p]
    exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < r)).mpr hrR)
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((N : ℝ) / p) (a / 2) (by positivity)).comp (largeScale_tendsto hr)
  have hlim' : Tendsto (fun n : ℕ => (n : ℝ) ^ N * Real.exp (-(a / 2) * largeScale r n))
      atTop (𝓝 0) := by
    convert hlim using 1
    funext n
    dsimp only [Function.comp_apply]
    rw [largeScale, ← Real.rpow_mul (Nat.cast_nonneg n), mul_div_cancel₀ _ hp.ne', Real.rpow_natCast]
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ hlim'
  have hsmall : ∀ᶠ n : ℕ in atTop, b * smallParameter r n < a / 2 :=
    ((smallParameter_tendsto (by omega : 0 < r)).const_mul b).eventually
      (gt_mem_nhds (by simpa using (show 0 < a / 2 by positivity)))
  filter_upwards [hsmall] with n hn
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _)
    (pow_nonneg (Nat.cast_nonneg n) N)
  have hR : 0 ≤ largeScale r n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  nlinarith [mul_le_mul_of_nonneg_left hn.le hR]

theorem HasLogNormGrowth.superpolynomial_separation
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    {r : ℕ} (hr : 1 < r) {s : ℕ → ℝ} {a b : ℝ} {v : ℕ → V} {w : ℕ → W}
    (hv : HasLogNormGrowth r s a v) (hw : HasLogNormGrowth r s b w) (hab : a < b) (N : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ N * (‖v n‖ / ‖w n‖)) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := hv
  obtain ⟨D, _, hD⟩ := hw
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _
    (tendsto_nat_pow_mul_exp_gap hr (sub_pos.mpr hab) (C + D) N)
  filter_upwards [hC, hD] with n hnV hnW
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg n) N)
  have he : ‖v n‖ / ‖w n‖ = Real.exp (Real.log ‖v n‖ - Real.log ‖w n‖) := by
    rw [Real.exp_sub, Real.exp_log hnV.1, Real.exp_log hnW.1]
  rw [he]
  apply Real.exp_le_exp.mpr
  have hlu := (abs_le.mp hnV.2).2
  have hwl := (abs_le.mp hnW.2).1
  nlinarith

theorem HasLogNormGrowth.isLittleO
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    {r : ℕ} (hr : 1 < r) {s : ℕ → ℝ} {a b : ℝ} {v : ℕ → V} {w : ℕ → W}
    (hv : HasLogNormGrowth r s a v) (hw : HasLogNormGrowth r s b w) (hab : a < b) :
    v =o[atTop] w := by
  have hlim : Tendsto (fun n => ‖v n‖ / ‖w n‖) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using hv.superpolynomial_separation hr hw hab 0
  have hden : ∀ᶠ n : ℕ in atTop, ‖w n‖ = 0 → ‖v n‖ = 0 :=
    hw.choose_spec.2.mono (fun _ hn he => (hn.1.ne' he).elim)
  exact ((Asymptotics.isLittleO_iff_tendsto' hden).mpr hlim).of_norm_left.of_norm_right

end ThisWork
