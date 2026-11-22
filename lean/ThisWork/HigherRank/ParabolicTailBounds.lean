module

public import ThisWork.HigherRank.ParabolicTailGeometry
public import ThisWork.HigherRank.ParabolicGap
public import ThisWork.HigherRank.ConeTailDecay
public import ThisWork.HigherRank.HankelTranslations

/-! Both infinite tails are exponentially small relative to the saddle
kernel, uniformly over small translations of a fixed parabolic contour. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem translated_power_tail_eq_cone (r m : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n k : ℕ) (L y : ℝ) (δ : ℂ) :
    (∫ u in Iic L, (δ + (u : ℂ) + (y : ℂ) * Complex.I) ^ k *
      kernel r m A z j n ((largeScale r n : ℂ) * (δ + (u : ℂ) + (y : ℂ) * Complex.I))) =
      ∫ t in Ioi (-L - δ.re), scaledLeftMomentKernel r m A z j n k (δ.im + y) t := by
  rw [translated_integral_Iic (fun s => s ^ k * kernel r m A z j n ((largeScale r n : ℂ) * s)) L y δ,
    show -L - δ.re = -(L + δ.re) by ring, add_comm δ.im y]
  simpa only [scaledLeftMomentKernel, Complex.ofReal_neg, neg_neg] using
    integral_comp_neg_Iic (L + δ.re) (scaledLeftMomentKernel r m A z j n k (y + δ.im))

theorem uniform_parabolic_power_tail_bound {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (m : ℕ) (j : ℤ) (k : ℕ) {a b h : ℝ} (ha : 0 < a) (hh : 0 < h)
    (hscale : saddleScale r A z = a ^ 2 + b ^ 2)
    (hj : (r : ℝ) * (2 * Real.arctan (b / a)) = -2 * Real.pi * j) :
    ∃ B > 0, |b| + h < B ∧ ∃ η > 0, ∃ g > 0, ∃ C > 0,
      ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ < η → ∀ e : ℝ, (e = 1 ∨ e = -1) →
        ‖∫ u in Iic (a ^ 2 - B ^ 2), (δ + (u : ℂ) + ((e * (2 * a * B) : ℝ) : ℂ) * Complex.I) ^ k *
          kernel r m A z j n ((largeScale r n : ℂ) *
            (δ + (u : ℂ) + ((e * (2 * a * B) : ℝ) : ℂ) * Complex.I))‖ ≤
          C * ‖kernel r m A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a b))‖ *
            Real.exp (-g * largeScale r n) / largeScale r n := by
  obtain ⟨T, _, htail⟩ := uniform_integrated_cone_moment_tail hr hA zero_lt_one m z j k
  obtain ⟨B, hB, hBb, hgeometry⟩ := exists_parabolic_cone_cutoff ha T b h
  have hbB : |b| ≤ B := by linarith [abs_nonneg h]
  have hBb' : |b| + h < B := by linarith [le_abs_self h]
  obtain ⟨d, hd, g, hg, hgap⟩ := uniform_kernel_parabolic_gap hr hA hz m j ha hbB hh hscale hj
  let C := Real.exp (B ^ 2 - a ^ 2 + 1)
  refine ⟨B, hB, hBb', min d 1, lt_min hd zero_lt_one, g, hg, C, Real.exp_pos _, ?_⟩
  filter_upwards [htail, hgap, eventually_gt_atTop (0 : ℕ)] with n hnT hnG hn0 δ hδ e he
  have hδd : ‖δ‖ < d := hδ.trans_le (min_le_left _ _)
  have hδ1 : ‖δ‖ ≤ 1 := (hδ.trans_le (min_le_right _ _)).le
  let t := B ^ 2 - a ^ 2 - δ.re
  let y := δ.im + e * (2 * a * B)
  have hgeom := hgeometry δ hδ1
  have hcone := hgeom.2 e he
  have hI := (hnT t hgeom.1 y hcone.1 hcone.2).2
  have hEB : e * B ∈ Icc (-B) B := by rcases he with rfl | rfl <;> constructor <;> nlinarith
  have hdist : h ≤ |e * B - b| := by
    have heB : |e * B| = B := by rcases he with rfl | rfl <;> simp [abs_of_pos hB]
    have hd := norm_sub_norm_le (e * B) b
    simp only [Real.norm_eq_abs, heB] at hd
    linarith
  have hgK := hnG δ hδd (e * B) hEB hdist
  have hpoint : -(t : ℂ) + (y : ℂ) * Complex.I = δ + parabolicPoint a (e * B) := by
    rcases he with rfl | rfl
    all_goals
      dsimp only [t, y]
      rw [parabolicPoint_eq_coordinates]
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] <;> ring
  rw [hpoint] at hI
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hexp : Real.exp t ≤ C := Real.exp_le_exp.mpr (by
    have hre := (Complex.abs_re_le_norm δ).trans hδ1
    dsimp only [t]
    linarith [(abs_le.mp hre).1])
  rw [translated_power_tail_eq_cone]
  rw [show -(a ^ 2 - B ^ 2) - δ.re = t by dsimp only [t]; ring]
  change ‖∫ t' in Ioi t, scaledLeftMomentKernel r m A z j n k y t'‖ ≤ _
  exact hI.trans (div_le_div_of_nonneg_right
    (by nlinarith [mul_le_mul hexp hgK (norm_nonneg _) (Real.exp_pos (B ^ 2 - a ^ 2 + 1)).le]) hR.le)

end ThisWork.HigherRank
