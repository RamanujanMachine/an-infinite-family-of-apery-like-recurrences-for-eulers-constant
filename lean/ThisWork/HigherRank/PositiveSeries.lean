module

public import ThisWork.HigherRank.Definitions
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The positive residue series in rank `p + 1`.
The real series exists in every rank. Its identification with a solution of
the original integral family is needed only in even rank and is separate. -/

@[expose] public section
namespace ThisWork.HigherRank.PositiveSeries

open Filter
open scoped Topology

noncomputable def term (p : ℕ) (A : Fin p → ℝ) (z : ℝ) (n k : ℕ) : ℝ :=
  z ^ k * (∏ i, Real.Gamma (A i * n + k + 1)) / (k.factorial : ℝ) ^ (p + 1)

noncomputable def ratio (p : ℕ) (A : Fin p → ℝ) (z : ℝ) (n k : ℕ) : ℝ :=
  z * (1 / ((k : ℝ) + 1)) * ∏ i, (1 + A i * n / ((k : ℝ) + 1))

theorem term_pos {p : ℕ} {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n k : ℕ) :
    0 < term p A z n k := by
  apply div_pos
  · apply mul_pos (pow_pos hz _)
    apply Finset.prod_pos
    intro i _
    apply Real.Gamma_pos_of_pos
    have hi := hA i
    positivity
  · positivity

theorem term_succ {p : ℕ} {A : Fin p → ℝ} (hA : ∀ i, 0 < A i)
    (z : ℝ) (n k : ℕ) :
    term p A z n (k + 1) =
      (z * ∏ i, (A i * n + k + 1)) / ((k : ℝ) + 1) ^ (p + 1) * term p A z n k := by
  have hΓ (i : Fin p) :
      Real.Gamma (A i * n + ((k : ℝ) + 1) + 1) =
        (A i * n + k + 1) * Real.Gamma (A i * n + k + 1) := by
    rw [show A i * n + ((k : ℝ) + 1) + 1 = (A i * n + k + 1) + 1 by ring]
    apply Real.Gamma_add_one
    have hi := hA i
    positivity
  unfold term
  simp only [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
  simp_rw [hΓ]
  rw [Finset.prod_mul_distrib, pow_succ, mul_pow]
  generalize (∏ i, (A i * n + k + 1)) = P
  generalize (∏ i, Real.Gamma (A i * n + k + 1)) = G
  field_simp

theorem ratio_eq (p : ℕ) (A : Fin p → ℝ) (z : ℝ) (n k : ℕ) :
    ratio p A z n k = (z * ∏ i, (A i * n + k + 1)) / ((k : ℝ) + 1) ^ (p + 1) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  have hi (i : Fin p) : 1 + A i * n / ((k : ℝ) + 1) =
      (A i * n + k + 1) / ((k : ℝ) + 1) := by
    field_simp
    ring
  unfold ratio
  simp_rw [hi]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_succ]
  generalize (∏ i, (A i * n + k + 1)) = P
  field_simp

theorem term_succ_normalized {p : ℕ} {A : Fin p → ℝ} (hA : ∀ i, 0 < A i)
    (z : ℝ) (n k : ℕ) :
    term p A z n (k + 1) = ratio p A z n k * term p A z n k := by
  rw [ratio_eq, term_succ hA]

theorem ratio_tendsto (p : ℕ) (A : Fin p → ℝ) (z : ℝ) (n : ℕ) :
    Tendsto (ratio p A z n) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => z * (1 / ((k : ℝ) + 1)) *
    ∏ i, (1 + A i * n / ((k : ℝ) + 1))) atTop (𝓝 0)
  have hdiv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hi (i : Fin p) :
      Tendsto (fun k : ℕ => 1 + A i * n / ((k : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero, mul_one_div] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hdiv)
  have hp := tendsto_finsetProd Finset.univ (fun i _ => hi i)
  simpa only [Finset.prod_const_one, mul_zero, zero_mul] using
    (tendsto_const_nhds.mul hdiv).mul hp

theorem term_summable {p : ℕ} {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n : ℕ) :
    Summable (term p A z n) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [(ratio_tendsto p A z n).eventually_lt_const
    (show (0 : ℝ) < 1 / 2 by norm_num)] with k hk
  rw [Real.norm_eq_abs, abs_of_pos (term_pos hA hz n (k + 1)),
    Real.norm_eq_abs, abs_of_pos (term_pos hA hz n k), term_succ_normalized hA]
  exact mul_le_mul_of_nonneg_right hk.le (term_pos hA hz n k).le

theorem ratio_antitone {p : ℕ} {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n : ℕ) :
    Antitone (ratio p A z n) := by
  intro k l hkl
  have hdiv : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hnonneg (j : ℕ) (i : Fin p) : 0 ≤ 1 + A i * n / ((j : ℝ) + 1) := by
    have hi := hA i
    positivity
  have hfactor (i : Fin p) :
      1 + A i * n / ((l : ℝ) + 1) ≤ 1 + A i * n / ((k : ℝ) + 1) := by
    have hi := hA i
    simpa only [mul_one_div, add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hdiv
        (mul_nonneg hi.le (Nat.cast_nonneg n))) 1
  unfold ratio
  exact mul_le_mul (mul_le_mul_of_nonneg_left hdiv hz.le)
    (Finset.prod_le_prod₀ (fun i _ => hnonneg l i) (fun i _ => hfactor i))
    (Finset.prod_nonneg (fun i _ => hnonneg l i)) (by positivity)

private theorem shifted_ratio_tendsto (u : ℝ) :
    Tendsto (fun k : ℕ => (u + k + 1) / (u + k)) atTop (𝓝 1) := by
  have hu : Tendsto (fun k : ℕ => u + (k : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop u tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun k : ℕ => 1 + (u + k)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero, Function.comp_apply] using
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hu)
  apply hlim.congr'
  filter_upwards [hu.eventually_gt_atTop 0] with k hk
  field_simp

/-- Every fixed polynomial moment is absolutely summable, in every rank. -/
theorem moment_summable {p : ℕ} {A : Fin p → ℝ} {z : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (n h : ℕ) (u : ℝ) :
    Summable (fun k : ℕ => (u + k) ^ h * term p A z n k) := by
  have hu : Tendsto (fun k : ℕ => u + (k : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop u tendsto_natCast_atTop_atTop
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · filter_upwards [hu.eventually_gt_atTop 0] with k hk
    exact mul_ne_zero (pow_ne_zero _ hk.ne') (term_pos hA hz n k).ne'
  · have hg : Tendsto (fun k : ℕ => ratio p A z n k *
        ((u + k + 1) / (u + k)) ^ h) atTop (𝓝 0) := by
      simpa only [one_pow, zero_mul] using
        (ratio_tendsto p A z n).mul ((shifted_ratio_tendsto u).pow h)
    apply hg.congr'
    filter_upwards [hu.eventually_gt_atTop 0] with k hk
    have hk1 : 0 < u + ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [Real.norm_of_nonneg (mul_nonneg (pow_pos hk1 _).le (term_pos hA hz n (k + 1)).le),
      Real.norm_of_nonneg (mul_nonneg (pow_pos hk _).le (term_pos hA hz n k).le),
      term_succ_normalized hA]
    simp only [Nat.cast_add, Nat.cast_one, div_pow, ← add_assoc]
    field_simp [(term_pos hA hz n k).ne']

end ThisWork.HigherRank.PositiveSeries
