module

public import ThisWork.ParabolicContour
public import ThisWork.LocalPhase

/-! Each half of a finite parabolic arc fits in a holomorphic disk whose
intersection with the real axis is strictly positive. This permits contour
deformation using primitives, without a general homotopy theorem. -/

@[expose] public section
namespace ThisWork

open Set Metric

theorem parabolic_disk_subset_slitPlane {a d Y : ℝ}
    (hd : 0 < d) (hda : d < a ^ 2) :
    ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)) ⊆
      Complex.slitPlane := by
  intro s hs
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : s.im = 0
  · left
    have hnorm : ‖s - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)‖ < Real.sqrt (Y ^ 2 + d ^ 2) :=
      by simpa only [mem_ball, dist_eq_norm] using hs
    have hsq := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnorm
    rw [Real.sq_sqrt (by positivity), Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im,
      mul_one, sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
      zero_add, hi] at hsq
    nlinarith [sq_nonneg (s.re - a ^ 2 + d)]
  · exact Or.inr hi

theorem norm_parabolicPoint_sub_upper_center_le {a B Y auxB : ℝ}
    (hY : 0 ≤ Y) (hb : auxB ∈ Icc 0 B)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ‖parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ Y := by
  have hb3 : auxB ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hb.1 hb.2 3
  have hb4 : auxB ^ 4 ≤ B ^ 3 * auxB := by
    nlinarith [mul_le_mul_of_nonneg_right hb3 hb.1]
  have hb2 : auxB ^ 2 ≤ B * auxB := by
    nlinarith [mul_le_mul_of_nonneg_right hb.2 hb.1]
  have ht := mul_le_mul_of_nonneg_left hb2 (by positivity : 0 ≤ 4 * a ^ 2)
  have hh := mul_le_mul_of_nonneg_right hheight hb.1
  apply (sq_le_sq₀ (norm_nonneg _) hY).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add,
    parabolicPoint_re, parabolicPoint_im]
  nlinarith

theorem translated_upper_parabola_mem_disk {a B Y d auxB : ℝ} {δ : ℂ}
    (hY : 0 ≤ Y) (hb : auxB ∈ Icc 0 B)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) :
    δ + parabolicPoint a auxB ∈
      ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)) := by
  rw [mem_ball, dist_eq_norm]
  calc
    _ = ‖δ + (parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I))‖ := by
      congr 1
      abel
    _ ≤ ‖δ‖ + ‖parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ ≤ ‖δ‖ + Y := add_le_add le_rfl (norm_parabolicPoint_sub_upper_center_le hY hb hheight)
    _ < _ := by linarith

theorem parabolic_disk_translation_margin_pos {Y d : ℝ} (hY : 0 ≤ Y) (hd : 0 < d) :
    0 < Real.sqrt (Y ^ 2 + d ^ 2) - Y := by
  apply sub_pos.mpr
  apply (sq_lt_sq₀ hY (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith

/-- Deformation of a translated parabolic half-arc to its chord. -/
theorem upper_parabolic_integral_eq_segment {a B Y d : ℝ} {δ : ℂ}
    (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)))) :
    (∫ auxB in (0 : ℝ)..B, (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) *
      f (δ + parabolicPoint a auxB)) =
      Neuschel.segmentIntegral f (δ + parabolicPoint a 0) (δ + parabolicPoint a B) := by
  apply Neuschel.contour_integral_eq_segment hB hf
  · unfold parabolicPoint
    fun_prop
  · fun_prop
  · intro auxB _
    exact (hasDerivAt_parabolicPoint a auxB).const_add δ
  · intro auxB hb
    exact translated_upper_parabola_mem_disk hY hb hheight hδ

theorem eventually_upper_parabolic_kernel_integral_eq_segment {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ)
    {a B Y d : ℝ} (hd : 0 < d) (hda : d < a ^ 2) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ k : ℕ, ∀ δ : ℂ,
      ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y →
      (∫ auxB in (0 : ℝ)..B, (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) *
        ((δ + parabolicPoint a auxB) ^ k *
          kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB)))) =
        Neuschel.segmentIntegral (fun s => s ^ k * kernel r b A z j n ((largeScale r n : ℂ) * s))
          (δ + parabolicPoint a 0) (δ + parabolicPoint a B) := by
  filter_upwards [eventually_differentiableOn_scaled_kernel_ball hr hA b z j
    (parabolic_disk_subset_slitPlane (Y := Y) hd hda)] with n hn k δ hδ
  apply upper_parabolic_integral_eq_segment hB hY hheight hδ
    (f := fun s => s ^ k * kernel r b A z j n ((largeScale r n : ℂ) * s))
  exact (differentiableOn_id.pow k).mul hn

theorem norm_parabolicPoint_sub_lower_center_le {a B Y auxB : ℝ}
    (hY : 0 ≤ Y) (hb : auxB ∈ Icc (-B) 0)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ‖parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I)‖ ≤ Y := by
  have hc : starRingEnd ℂ
      (parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I)) =
      parabolicPoint a (-auxB) - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) := by
    simp [parabolicPoint]
  have h := norm_parabolicPoint_sub_upper_center_le hY
    (show -auxB ∈ Icc 0 B by constructor <;> linarith [hb.1, hb.2]) hheight
  rw [← hc, Complex.norm_conj] at h
  exact h

theorem translated_lower_parabola_mem_disk {a B Y d auxB : ℝ} {δ : ℂ}
    (hY : 0 ≤ Y) (hb : auxB ∈ Icc (-B) 0)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) :
    δ + parabolicPoint a auxB ∈
      ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)) := by
  rw [mem_ball, dist_eq_norm]
  calc
    _ = ‖δ + (parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I))‖ := by
      congr 1
      abel
    _ ≤ ‖δ‖ + ‖parabolicPoint a auxB - (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ ≤ ‖δ‖ + Y := add_le_add le_rfl (norm_parabolicPoint_sub_lower_center_le hY hb hheight)
    _ < _ := by linarith

theorem lower_parabolic_integral_eq_segment {a B Y d : ℝ} {δ : ℂ}
    (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)))) :
    (∫ auxB in (-B)..(0 : ℝ), (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) *
      f (δ + parabolicPoint a auxB)) =
      Neuschel.segmentIntegral f (δ + parabolicPoint a (-B)) (δ + parabolicPoint a 0) := by
  apply Neuschel.contour_integral_eq_segment (by linarith : -B ≤ 0) hf
  · unfold parabolicPoint
    fun_prop
  · fun_prop
  · intro auxB _
    exact (hasDerivAt_parabolicPoint a auxB).const_add δ
  · intro auxB hb
    exact translated_lower_parabola_mem_disk hY hb hheight hδ

end ThisWork
