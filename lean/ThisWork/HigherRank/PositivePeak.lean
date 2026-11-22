module

public import ThisWork.HigherRank.PositiveSeries
public import ThisWork.HigherRank.Scales

/-! The coefficient ratio at the natural saddle scale in arbitrary rank. -/

@[expose] public section
namespace ThisWork.HigherRank.PositiveSeries

open Filter
open scoped Topology

theorem ratio_rescaled (p : ℕ) (A : Fin p → ℝ) (z : ℝ) {n : ℕ} (hn : 0 < n)
    (k : ℕ) {R : ℝ} (hR : R ^ (p + 1) = (n : ℝ) ^ p) :
    ratio p A z n k = z * (∏ i, (A i + ((k : ℝ) + 1) / n)) /
      (((k : ℝ) + 1) / R) ^ (p + 1) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hi (i : Fin p) : A i + ((k : ℝ) + 1) / n =
      (A i * n + k + 1) / n := by field_simp; ring
  rw [ratio_eq]
  simp_rw [hi]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
  rw [hR]
  generalize (∏ i, (A i * n + k + 1)) = P
  field_simp

/-- If the summation index is asymptotic to `u * n^(p/(p+1))`, its coefficient
ratio tends to `z * prod A / u^(p+1)`. This keeps `z` symbolic. -/
theorem ratio_tendsto_at_scale {p : ℕ} (hp : 0 < p) (A : Fin p → ℝ) (z : ℝ)
    {k : ℕ → ℕ} {u : ℝ} (hu : 0 < u)
    (hk : Tendsto (fun n => (k n : ℝ) / largeScale (p + 1) n) atTop (𝓝 u)) :
    Tendsto (fun n => ratio p A z n (k n)) atTop
      (𝓝 (z * (∏ i, A i) / u ^ (p + 1))) := by
  have hp1 : 1 < p + 1 := by omega
  have hR := largeScale_tendsto hp1
  have hplus : Tendsto (fun n => ((k n : ℝ) + 1) / largeScale (p + 1) n)
      atTop (𝓝 u) := by
    simpa only [add_div, one_div, Function.comp_apply, add_zero] using
      hk.add (tendsto_inv_atTop_zero.comp hR)
  have hsmall : Tendsto (fun n => ((k n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    have hm := hplus.mul (largeScale_div_nat_tendsto (show 0 < p + 1 by omega))
    simp only [mul_zero] at hm
    apply hm.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hRn : largeScale (p + 1) n ≠ 0 :=
      (Real.rpow_pos_of_pos hnR _).ne'
    field_simp
  have hi (i : Fin p) :
      Tendsto (fun n => A i + ((k n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 (A i)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hsmall
  have hprod := tendsto_finsetProd Finset.univ (fun i _ => hi i)
  have hlim := (hprod.const_mul z).div (hplus.pow (p + 1))
    (pow_ne_zero _ hu.ne')
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (ratio_rescaled p A z hn (k n)
    (by simpa only [Nat.add_sub_cancel_right] using
      largeScale_pow (show 0 < p + 1 by omega) n)).symm

theorem floor_scaled_tendsto {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n => (⌊u * largeScale (p + 1) n⌋₊ : ℝ) / largeScale (p + 1) n)
      atTop (𝓝 u) := by
  have hR := largeScale_tendsto (show 1 < p + 1 by omega)
  have hfloor := tendsto_nat_floor_div_atTop.comp (hR.const_mul_atTop hu)
  have hlim := hfloor.mul_const u
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hRn : largeScale (p + 1) n ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne'
  simp only [Function.comp_apply]
  field_simp

theorem eventually_tail_ratio_bound {p : ℕ} (hp : 0 < p) {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) {u q : ℝ} (hu : 0 < u)
    (hq : z * (∏ i, A i) / u ^ (p + 1) < q) :
    ∀ᶠ n : ℕ in atTop, ∀ k ≥ ⌊u * largeScale (p + 1) n⌋₊,
      ratio p A z n k ≤ q := by
  have hf := (ratio_tendsto_at_scale hp A z hu (floor_scaled_tendsto hp hu)).eventually_lt_const hq
  filter_upwards [hf] with n hn k hk
  exact (ratio_antitone hA hz n hk).trans hn.le

theorem tail_term_le_geometric {p : ℕ} {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n K : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hK : ratio p A z n K ≤ q) (j : ℕ) :
    term p A z n (K + j) ≤ q ^ j * term p A z n K := by
  induction j with
  | zero => simp only [Nat.add_zero, pow_zero, one_mul, le_refl]
  | succ j ih =>
    rw [Nat.add_succ, term_succ_normalized hA]
    have hr := (ratio_antitone hA hz n (Nat.le_add_right K j)).trans hK
    calc
      _ ≤ q * term p A z n (K + j) :=
        mul_le_mul_of_nonneg_right hr (term_pos hA hz n (K + j)).le
      _ ≤ q * (q ^ j * term p A z n K) := mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ]; ring

theorem tail_sum_le_geometric {p : ℕ} {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n K : ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : ratio p A z n K ≤ q) :
    (∑' j, term p A z n (K + j)) ≤ term p A z n K / (1 - q) := by
  have hs : Summable (fun j => term p A z n (K + j)) :=
    (term_summable hA hz n).comp_injective (add_right_injective K)
  have hg := (summable_geometric_of_lt_one hq hq1).mul_right (term p A z n K)
  calc
    _ ≤ ∑' j, q ^ j * term p A z n K :=
      Summable.tsum_le_tsum (fun j => tail_term_le_geometric hA hz n K hq hK j) hs hg
    _ = _ := by rw [tsum_mul_right, tsum_geometric_of_lt_one hq hq1]; ring

end ThisWork.HigherRank.PositiveSeries
