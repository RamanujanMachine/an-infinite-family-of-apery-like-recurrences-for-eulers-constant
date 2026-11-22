module

public import ThisWork.HigherRank.ReflectedSaddleEquation
public import ThisWork.HigherRank.SaddleEquation
public import ThisWork.HigherRank.Regions

/-! Quantitative limiting equations for the regular reflected kernel used
at the even-rank boundary saddle. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem uniform_scaled_reflected_digamma_region {r : ℕ} (hr : 3 ≤ r)
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, κ ≤ -s.re ∨ η ≤ |s.im| →
      ‖Complex.digamma (1 - (largeScale r n : ℂ) * s) -
        Complex.log ((largeScale r n : ℂ) * (-s))‖ ≤
          (2 / κ + 1 + 9 / η + 4 * Real.pi + 1 / min κ η) * smallParameter r n := by
  filter_upwards [uniform_scaled_digamma_region_smallParameter hr hκ hη,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 s hs
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have hμ : 0 < min κ η := lt_min hκ hη
  have hreg : κ ≤ (-s).re ∨ η ≤ |(-s).im| := by simpa only [Complex.neg_re, Complex.neg_im, abs_neg] using hs
  have hslit := region_mem_slitPlane hκ hη hreg
  let w : ℂ := (largeScale r n : ℂ) * (-s)
  have hwslit : w ∈ Complex.slitPlane := by
    apply (ThisWork.div_pos_real_mem_slitPlane_iff hR w).mp
    simpa only [w, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')] using hslit
  have hnorm : min κ η ≤ ‖s‖ := by
    rcases hs with hre | him
    · exact (min_le_left _ _).trans (hre.trans ((neg_le_abs s.re).trans (Complex.abs_re_le_norm s)))
    · exact (min_le_right _ _).trans (him.trans (Complex.abs_im_le_norm s))
  have hwNorm : largeScale r n * min κ η ≤ ‖w‖ := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_of_nonneg hR.le, norm_neg]
    exact mul_le_mul_of_nonneg_left hnorm hR.le
  have hinv : ‖w⁻¹‖ ≤ (1 / min κ η) * smallParameter r n := by
    rw [norm_inv, ← one_div]
    calc
      _ ≤ 1 / (largeScale r n * min κ η) := one_div_le_one_div_of_le (mul_pos hR hμ) hwNorm
      _ = (1 / min κ η) * (1 / largeScale r n) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_largeScale_le_smallParameter hr hn1) (by positivity)
  have hψ := hn (-s) hreg
  have he : 1 - (largeScale r n : ℂ) * s = w + 1 := by dsimp only [w]; ring
  rw [he, Complex.digamma_apply_add_one w (Analytic.not_neg_nat_of_mem_slitPlane hwslit)]
  calc
    _ = ‖(Complex.digamma w - Complex.log w) + w⁻¹‖ := by congr 1; ring
    _ ≤ ‖Complex.digamma w - Complex.log w‖ + ‖w⁻¹‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

noncomputable def reflectedEquation (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (r : ℂ) * Complex.digamma (1 - (largeScale r n : ℂ) * s) -
    (∑ i, Complex.digamma ((A i : ℂ) * n - (largeScale r n : ℂ) * s + 1)) - (Real.log z : ℂ)

noncomputable def reflectedLimitingEquation (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (s : ℂ) : ℂ :=
  (r : ℂ) * Complex.log (-s) - (∑ i, (Real.log (A i) : ℂ)) - (Real.log z : ℂ)

theorem reflectedEquation_sub_limit {r : ℕ} (hr : 0 < r) {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (z : ℝ) {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 0) :
    reflectedEquation r A z n s - reflectedLimitingEquation r A z s =
      (r : ℂ) * (Complex.digamma (1 - (largeScale r n : ℂ) * s) -
        Complex.log ((largeScale r n : ℂ) * (-s))) -
      ∑ i, (Complex.digamma ((A i : ℂ) * n - (largeScale r n : ℂ) * s + 1) -
        Complex.log ((A i * n : ℝ) : ℂ)) := by
  have h := exactSaddleEquation_sub_limit hr hA z 0 hn (neg_ne_zero.mpr hs)
  unfold exactSaddleEquation limitingEquation at h
  unfold reflectedEquation reflectedLimitingEquation
  simp only [Int.cast_zero, mul_zero, add_zero, Finset.sum_sub_distrib] at h ⊢
  linear_combination h

theorem uniform_reflectedEquation_region {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ)
    {κ η M : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ -s.re ∨ η ≤ |s.im| →
      ‖reflectedEquation r A z n s - reflectedLimitingEquation r A z s‖ ≤ C * smallParameter r n := by
  let D := 2 / κ + 1 + 9 / η + 4 * Real.pi + 1 / min κ η
  let C := (r : ℝ) * D + ∑ i, ((11 + 3 * M) / (2 * A i))
  have hD : 0 ≤ D := by have hm := lt_min hκ hη; dsimp only [D]; positivity
  refine ⟨C, add_nonneg (mul_nonneg (Nat.cast_nonneg _) hD)
    (Finset.sum_nonneg (fun i _ => by have hi := hA i; positivity)), ?_⟩
  have hupper : ∀ᶠ n : ℕ in atTop, ∀ i, 4 ≤ A i * n ∧ largeScale r n * M ≤ (A i * n) / 4 :=
    Filter.eventually_all.mpr (fun i => eventually_affine_conditions (by omega : 0 < r) (hA i) M)
  filter_upwards [uniform_scaled_reflected_digamma_region hr hκ hη, hupper,
    eventually_ge_atTop (1 : ℕ)] with n hψ hupper hn1 s hs hreg
  have hs0 : s ≠ 0 := by
    intro he
    rw [he, Complex.zero_re, Complex.zero_im, neg_zero, abs_zero] at hreg
    rcases hreg with h | h <;> linarith
  rw [reflectedEquation_sub_limit (by omega : 0 < r) hA z (by omega : 0 < n) hs0]
  have hR : 0 ≤ largeScale r n := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega : 0 < n)) _).le
  calc
    _ ≤ ‖(r : ℂ) * (Complex.digamma (1 - (largeScale r n : ℂ) * s) -
        Complex.log ((largeScale r n : ℂ) * (-s)))‖ +
        ‖∑ i, (Complex.digamma ((A i : ℂ) * n - (largeScale r n : ℂ) * s + 1) -
          Complex.log ((A i * n : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) * (D * smallParameter r n) +
        ∑ i, (((11 + 3 * M) / (2 * A i)) * smallParameter r n) := by
      rw [norm_mul, Complex.norm_natCast]
      apply add_le_add (mul_le_mul_of_nonneg_left (hψ s hreg) (Nat.cast_nonneg _))
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      have h := Analytic.norm_digamma_affine_sub_log_le (hupper i).1 hR (hupper i).2 hs
      have he := affineError_le_smallParameter (show 1 ≤ r by omega) hn1 (hA i) M
      simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using h.trans he
    _ = _ := by rw [← Finset.sum_mul]; dsimp only [C]; ring

end ThisWork.HigherRank
