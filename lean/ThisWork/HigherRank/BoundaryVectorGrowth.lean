module

public import ThisWork.HigherRank.BoundaryMomentUpper
public import ThisWork.HigherRank.BoundaryFiniteMoments

/-! Growth of the complete even-rank auxiliary boundary vector. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter MeasureTheory
open scoped Topology

theorem weighted_boundary_hankel_split {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (z : ℝ) (n k : ℕ) {L : ℝ} (hL : L < 1) :
    hankelIntegral (1 / 2) 1 (fun x => (-x) ^ k * boundaryKernel r 0 A z n x) =
      (∫ u in Iic L, (-((u : ℂ) - Complex.I)) ^ k *
        boundaryKernel r 0 A z n ((u : ℂ) - Complex.I)) -
      (∫ u in Iic L, (-((u : ℂ) + Complex.I)) ^ k *
        boundaryKernel r 0 A z n ((u : ℂ) + Complex.I)) +
      boundaryFiniteMoment r A z n k L := by
  have hi (a y : ℝ) (ha : a < 1) (hy : |y| = 1) :
      IntegrableOn (fun u : ℝ => (-((u : ℂ) + (y : ℂ) * Complex.I)) ^ k *
        boundaryKernel r 0 A z n ((u : ℂ) + (y : ℂ) * Complex.I)) (Iic a) := by
    simpa only [Nat.cast_zero, zero_mul, zero_sub] using
      integrableOn_weighted_boundary_horizontal hr hA half hrh 0 z n k ha hy
  have hlo := intervalIntegral.integral_Iic_sub_Iic (hi L (-1) hL (by norm_num))
    (hi (1 / 2) (-1) (by norm_num) (by norm_num))
  have hhi := intervalIntegral.integral_Iic_sub_Iic (hi L 1 hL (by norm_num))
    (hi (1 / 2) 1 (by norm_num) (by norm_num))
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] at hlo hhi
  simp only [hankelIntegral, boundaryFiniteMoment, Complex.ofReal_one, one_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  linear_combination hlo - hhi

theorem weighted_boundary_hankel_upper {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖hankelIntegral (1 / 2) 1 (fun x => (-x) ^ k * boundaryKernel r 0 A z n x)‖ ≤
        commonScale r 0 A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n +
          C * (largeScale r n * smallParameter r n)) := by
  let L := -(6 * (r : ℝ))
  have hL : L < 1 := by dsimp only [L]; have hp : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); linarith
  have hLh : L ≤ 1 / 2 := by dsimp only [L]; have hp : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega); linarith
  obtain ⟨C, hC, hb⟩ := boundary_moment_bank_upper hr hA hz half hrh k
  obtain ⟨D, hD, hreal⟩ := reflectedRealIntegral_upper hr hA hz half hrh hL 0
  have hfinite := (boundaryFiniteMoment_polynomial_bound (by omega : 0 < r) hA hz k hLh).eventually_le_reflectedRealIntegral hr hA hz half hrh hL 0 (by norm_num : (0 : ℝ) < 1)
  let E := max C D
  refine ⟨E + 3, by dsimp only [E]; positivity, ?_⟩
  filter_upwards [hb, hreal, hfinite, eventually_ge_atTop (1 : ℕ)] with n hn hnR hnF hn1
  let e := largeScale r n * smallParameter r n
  let M := commonScale r 0 A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n + E * e)
  have he : 1 ≤ e := one_le_errorScale hr hn1
  have hs := (commonScale_pos hA hz 0 n).le
  have hCexp : commonScale r 0 A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n + C * e) ≤ M :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [le_max_left C D])) hs
  have hDexp : commonScale r 0 A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n + D * e) ≤ M :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [le_max_right C D])) hs
  have hm := (hn (-1) (Or.inr rfl)).trans hCexp
  have hp := (hn 1 (Or.inl rfl)).trans hCexp
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg] at hm hp
  have hf : ‖boundaryFiniteMoment r A z n k L‖ ≤ M := by
    simp only [one_mul] at hnF
    exact hnF.trans (hnR.trans hDexp)
  rw [weighted_boundary_hankel_split (by omega : 0 < r) hA half hrh z n k hL]
  calc
    _ ≤ 3 * M := by
      apply (norm_add_le _ _).trans
      apply (add_le_add (norm_sub_le _ _) le_rfl).trans
      linarith
    _ ≤ M * Real.exp (3 * e) := by
      have h3 : 3 ≤ Real.exp (3 * e) := by linarith [Real.add_one_le_exp (3 * e)]
      nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ M by dsimp only [M]; positivity)]
    _ = _ := by dsimp only [M, e]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem boundary_vector_zeroCenter_upper {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖boundaryIntegral r 0 A z n‖ ≤ commonScale r 0 A z n *
        Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n +
          C * (largeScale r n * smallParameter r n)) := by
  classical
  choose C hC hb using (fun k : Fin r => weighted_boundary_hankel_upper hr hA hz half hrh k.val)
  refine ⟨∑ k, C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  filter_upwards [Filter.eventually_all.mpr hb, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have he : 0 ≤ largeScale r n * smallParameter r n := (one_le_errorScale hr hn1).trans' zero_le_one
  have hw : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ ≤ 1 := by
    simp only [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
    apply inv_le_one_of_one_le₀
    linarith [Real.pi_gt_three]
  have hs := commonScale_pos hA hz 0 n
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  change ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _‖ ≤ _
  rw [norm_mul]
  have hsum : C k ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ k)
  have hb' := hn k
  simp only [Nat.cast_zero, zero_mul, zero_sub] at *
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (hb'.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
      (commonScale_pos hA hz 0 n).le))

theorem boundary_vector_zeroCenter_growth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      0 < ‖boundaryIntegral r 0 A z n‖ ∧
      |Real.log ‖boundaryIntegral r 0 A z n‖ - Real.log (commonScale r 0 A z n) -
        (r : ℝ) * saddleScale r A z * largeScale r n| ≤
          C * (largeScale r n * smallParameter r n) := by
  obtain ⟨C, hC, hl⟩ := boundary_integral_growth hr hA hz half hrh 0
  obtain ⟨D, hD, hu⟩ := boundary_vector_zeroCenter_upper hr hA hz half hrh
  refine ⟨C + D, by positivity, ?_⟩
  filter_upwards [hl, hu, eventually_boundary_hankel_ne_zero hr hA hz half hrh 0,
    eventually_ge_atTop (1 : ℕ)] with n hnL hnU hn0 hn1
  let k : Fin r := ⟨0, by omega⟩
  have hcf : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := inv_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  have hzero : boundaryIntegral r 0 A z n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      hankelIntegral (1 / 2) 1 (boundaryKernel r 0 A z n) := by
    simp only [boundaryIntegral, k, pow_zero, one_mul]
  have hpos0 : 0 < ‖boundaryIntegral r 0 A z n k‖ := by rw [hzero]; exact norm_pos_iff.mpr (mul_ne_zero hcf hn0)
  have hpos := hpos0.trans_le (norm_le_pi_norm (boundaryIntegral r 0 A z n) k)
  refine ⟨hpos, ?_⟩
  have hlo := Real.log_le_log hpos0 (norm_le_pi_norm (boundaryIntegral r 0 A z n) k)
  rw [hzero] at hlo
  have hup := Real.log_le_log hpos hnU
  rw [Real.log_mul (commonScale_pos hA hz 0 n).ne' (Real.exp_ne_zero _), Real.log_exp] at hup
  have he : 0 ≤ largeScale r n * smallParameter r n := (one_le_errorScale hr hn1).trans' zero_le_one
  exact abs_le.mpr ⟨by nlinarith [(abs_le.mp hnL).1], by nlinarith⟩

end ThisWork.HigherRank
