module

public import ThisWork.HigherRank.ScaledShiftedHankel
public import ThisWork.HigherRank.ConeTailDecay

/-! The defining Gamma integrals equal a finite translated parabolic arc
with its two absolutely convergent horizontal tails. The translation may
depend on the index, and the estimate is uniform on a fixed neighborhood. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable def scaledWeightedKernel (r m : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n k : ℕ) (s : ℂ) : ℂ :=
  ((m : ℂ) * n - (largeScale r n : ℂ) * s) ^ k * kernel r m A z j n ((largeScale r n : ℂ) * s)

theorem eventually_branchIntegral_eq_parabolic_with_tails {r : ℕ} (hr : 1 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (j : ℤ)
    {a B Y d : ℝ} (ha : 0 < a) (hB : 0 < B) (hY : 0 ≤ Y) (hd : 0 < d) (hda : d < a ^ 2)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ∃ η > 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ < η → ∀ k : Fin r,
      branchIntegral r m A z j n k =
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (largeScale r n : ℂ) *
        ((∫ u in Iic (a ^ 2 - B ^ 2), scaledWeightedKernel r m A z j n k.val
            (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I)) +
          parabolicArcIntegral a B δ (scaledWeightedKernel r m A z j n k.val) -
          (∫ u in Iic (a ^ 2 - B ^ 2), scaledWeightedKernel r m A z j n k.val
            (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I))) := by
  let margin := Real.sqrt (Y ^ 2 + d ^ 2) - Y
  let η := min margin (min (a ^ 2 / 8) (a * B))
  have hmargin : 0 < margin := parabolic_disk_translation_margin_pos hY hd
  have hη : 0 < η := lt_min hmargin (lt_min (by positivity) (mul_pos ha hB))
  have hup := parabolic_disk_subset_slitPlane (Y := Y) hd hda
  have hdown : ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I)
      (Real.sqrt (Y ^ 2 + d ^ 2)) ⊆ Complex.slitPlane := by
    simpa only [neg_sq, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      (parabolic_disk_subset_slitPlane (Y := -Y) hd hda)
  refine ⟨η, hη, ?_⟩
  filter_upwards [eventually_differentiableOn_scaled_kernel_ball (by omega : 0 < r) hA m z j hup,
    eventually_differentiableOn_scaled_kernel_ball (by omega : 0 < r) hA m z j hdown,
    eventually_scaled_slit_in_kernelDomain (by omega : 0 < r) hA (2 * a ^ 2),
    (largeScale_tendsto hr).eventually (eventually_ge_atTop (1 / (a * B))),
    eventually_gt_atTop (0 : ℕ)] with n hfp hfm hdom hRab hn0 δ hδ k
  let R := largeScale r n
  have hR : 0 < R := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hδmargin : ‖δ‖ < margin := hδ.trans_le (min_le_left _ _)
  have hδa : ‖δ‖ ≤ a ^ 2 / 8 := (hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδB : ‖δ‖ ≤ a * B := (hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hre : |δ.re| ≤ a ^ 2 / 8 := (Complex.abs_re_le_norm δ).trans hδa
  have him : |δ.im| ≤ a * B := (Complex.abs_im_le_norm δ).trans hδB
  have hrightpos : 0 < a ^ 2 + δ.re := by have h := (abs_le.mp hre).1; nlinarith [sq_pos_of_pos ha]
  have hright0 : 0 < R * (a ^ 2 + δ.re) := mul_pos hR hrightpos
  have hright (i : Fin (r - 1)) : R * (a ^ 2 + δ.re) < A i * n + 1 := by
    have hqslit : (((a ^ 2 + δ.re : ℝ) : ℂ)) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hrightpos)
    have hx := hdom (((a ^ 2 + δ.re : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; nlinarith [(abs_le.mp hre).2])
      hqslit
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hx.2 i
  have hRab' : 1 ≤ R * (a * B) := by
    have hh := (div_le_iff₀ (mul_pos ha hB)).mp hRab
    nlinarith
  have hlow : R * (-(2 * a * B) + δ.im) ≤ -1 := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp him).2 hR.le
    nlinarith
  have hhigh : 1 ≤ R * (2 * a * B + δ.im) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp him).1 hR.le
    nlinarith
  have hp : DifferentiableOn ℂ (scaledWeightedKernel r m A z j n k.val)
      (ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2))) :=
    (by fun_prop : DifferentiableOn ℂ (fun s : ℂ => ((m : ℂ) * n - (largeScale r n : ℂ) * s) ^ k.val) _).mul hfp
  have hm : DifferentiableOn ℂ (scaledWeightedKernel r m A z j n k.val)
      (ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2))) :=
    (by fun_prop : DifferentiableOn ℂ (fun s : ℂ => ((m : ℂ) * n - (largeScale r n : ℂ) * s) ^ k.val) _).mul hfm
  have hilow : IntegrableOn (fun u : ℝ => scaledWeightedKernel r m A z j n k.val
      (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I)) (Iic (a ^ 2)) := by
    have habs : 1 ≤ |R * (-(2 * a * B) + δ.im)| := by linarith [neg_le_abs (R * (-(2 * a * B) + δ.im))]
    simpa only [scaledWeightedKernel, R, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      integrableOn_scaled_shifted_weighted_horizontal (by omega : 0 < r) hA m z j n k.val hR hright habs
  have hihigh : IntegrableOn (fun u : ℝ => scaledWeightedKernel r m A z j n k.val
      (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I)) (Iic (a ^ 2)) := by
    have habs : 1 ≤ |R * (2 * a * B + δ.im)| := hhigh.trans (le_abs_self _)
    exact integrableOn_scaled_shifted_weighted_horizontal (by omega : 0 < r) hA m z j n k.val hR hright habs
  have hfull := shifted_hankel_eq_parabolic_with_tails ha hB.le hY hheight hδmargin hp hm hilow hihigh
  have horig := branchIntegral_eq_scaled_shifted (by omega : 0 < r) hA m z j n k
    hR hright0 hright hlow hhigh
  change _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ((R : ℂ) * shiftedHankelIntegral (a ^ 2) (2 * a * B) δ (scaledWeightedKernel r m A z j n k.val)) at horig
  rw [hfull] at horig
  simpa only [mul_assoc] using horig

end ThisWork.HigherRank
