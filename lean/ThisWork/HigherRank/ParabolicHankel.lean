module

public import ThisWork.HigherRank.ParabolicPolygon
public import ThisWork.Definitions

/-! Exact attachment of the horizontal Hankel tails to the finite parabolic
arc. Translations are retained, so the contour can pass through a moving saddle. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Metric MeasureTheory

theorem parabolicPoint_eq_coordinates (a b : ℝ) :
    parabolicPoint a b = ((a ^ 2 - b ^ 2 : ℝ) : ℂ) + ((2 * a * b : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [parabolicPoint_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  · simp only [parabolicPoint_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

noncomputable def parabolicArcIntegral (a B : ℝ) (δ : ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ b in (-B)..B, (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) * f (δ + parabolicPoint a b)

theorem parabolicArcIntegral_const_mul (a B : ℝ) (δ c : ℂ) (f : ℂ → ℂ) :
    parabolicArcIntegral a B δ (fun s => c * f s) = c * parabolicArcIntegral a B δ f := by
  rw [parabolicArcIntegral, parabolicArcIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

noncomputable def shiftedHankelIntegral (right height : ℝ) (δ : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ u in Iic right, f (δ + (u : ℂ) - (height : ℂ) * Complex.I)) +
    (∫ y in -height..height, Complex.I * f (δ + (right : ℂ) + (y : ℂ) * Complex.I)) -
    ∫ u in Iic right, f (δ + (u : ℂ) + (height : ℂ) * Complex.I)

theorem finite_parabolic_integral_eq_polygon {a B Y d : ℝ} {δ : ℂ}
    (ha : 0 < a) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) {f : ℂ → ℂ}
    (hp : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2))))
    (hm : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)))) :
    parabolicArcIntegral a B δ f =
      (∫ u in (a ^ 2 - B ^ 2)..a ^ 2, f (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I)) +
      (∫ y in (-(2 * a * B))..(2 * a * B), Complex.I * f (δ + ((a ^ 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ u in (a ^ 2 - B ^ 2)..a ^ 2, f (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I)) := by
  let R := Real.sqrt (Y ^ 2 + d ^ 2)
  let cp := ((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I
  let cm := ((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I
  let P0 := δ + parabolicPoint a 0
  let Pp := δ + parabolicPoint a B
  let Pm := δ + parabolicPoint a (-B)
  let Cp := δ + parabolicCorner a B
  let Cm := δ + parabolicCorner a (-B)
  have h0p : P0 ∈ ball cp R := translated_upper_parabola_mem_disk hY ⟨le_rfl, hB⟩ hheight hδ
  have h0m : P0 ∈ ball cm R := translated_lower_parabola_mem_disk hY ⟨by linarith, le_rfl⟩ hheight hδ
  have hpp : Pp ∈ ball cp R := translated_upper_parabola_mem_disk hY ⟨hB, le_rfl⟩ hheight hδ
  have hmm : Pm ∈ ball cm R := translated_lower_parabola_mem_disk hY ⟨le_rfl, by linarith⟩ hheight hδ
  have hcp : Cp ∈ ball cp R := translated_mem_parabolic_disk
    (norm_parabolicCorner_sub_upper_center_le ha hB hY hheight) hδ
  have hcm : Cm ∈ ball cm R := translated_mem_parabolic_disk
    (norm_parabolicCorner_sub_lower_center_le ha hB hY hheight) hδ
  have hP0 : P0 = δ + ((a ^ 2 : ℝ) : ℂ) := by simp [P0, parabolicPoint_eq_coordinates]
  have hPp : Pp = δ + ((a ^ 2 - B ^ 2 : ℝ) : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I := by
    dsimp only [Pp]
    rw [parabolicPoint_eq_coordinates]; ring
  have hPm : Pm = δ + ((a ^ 2 - B ^ 2 : ℝ) : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I := by
    dsimp only [Pm]
    rw [parabolicPoint_eq_coordinates]; push_cast; ring
  have hCp : Cp = δ + ((a ^ 2 : ℝ) : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I := by
    dsimp only [Cp, parabolicCorner]; ring
  have hCm : Cm = δ + ((a ^ 2 : ℝ) : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I := by
    dsimp only [Cm, parabolicCorner]; push_cast; ring
  have hVp : (∫ y in (0 : ℝ)..(2 * a * B), Complex.I *
      f (δ + ((a ^ 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) = Neuschel.segmentIntegral f P0 Cp := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, hP0, hCp] using
      affine_integral_eq_segment hp (q := δ + ((a ^ 2 : ℝ) : ℂ)) (v := Complex.I)
        (a := 0) (b := 2 * a * B) (by simpa only [Complex.ofReal_zero, zero_mul, add_zero, ← hP0] using h0p)
        (by simpa only [← hCp] using hcp)
  have hVm : (∫ y in (-(2 * a * B))..(0 : ℝ), Complex.I *
      f (δ + ((a ^ 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) = Neuschel.segmentIntegral f Cm P0 := by
    simpa only [Complex.ofReal_zero, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
      zero_mul, add_zero, hP0, hCm] using
      affine_integral_eq_segment hm (q := δ + ((a ^ 2 : ℝ) : ℂ)) (v := Complex.I)
        (a := -(2 * a * B)) (b := 0)
        (by simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, ← hCm] using hcm)
        (by simpa only [Complex.ofReal_zero, zero_mul, add_zero, ← hP0] using h0m)
  have hHp : (∫ u in (a ^ 2 - B ^ 2)..a ^ 2,
      f (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I)) = Neuschel.segmentIntegral f Pp Cp := by
    simpa only [one_mul, mul_one, add_right_comm, hPp, hCp] using
      affine_integral_eq_segment hp (q := δ + ((2 * a * B : ℝ) : ℂ) * Complex.I) (v := 1)
        (a := a ^ 2 - B ^ 2) (b := a ^ 2)
        (by simpa only [mul_one, add_right_comm, ← hPp] using hpp)
        (by simpa only [mul_one, add_right_comm, ← hCp] using hcp)
  have hHm : (∫ u in (a ^ 2 - B ^ 2)..a ^ 2,
      f (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I)) = Neuschel.segmentIntegral f Pm Cm := by
    rw [hPm, hCm]
    simpa only [one_mul, mul_one, sub_eq_add_neg, add_right_comm] using
      affine_integral_eq_segment hm (q := δ - ((2 * a * B : ℝ) : ℂ) * Complex.I) (v := 1)
        (a := a ^ 2 + -(B ^ 2)) (b := a ^ 2)
        (by have hh := hmm; rw [hPm] at hh
            simpa only [mul_one, sub_eq_add_neg, add_right_comm, cm, R] using hh)
        (by have hh := hcm; rw [hCm] at hh
            simpa only [mul_one, sub_eq_add_neg, add_right_comm, cm, R] using hh)
  have hIp : IntervalIntegrable (fun b : ℝ => (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) *
      f (δ + parabolicPoint a b)) volume 0 B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hB
    exact (by fun_prop : ContinuousOn (fun b : ℝ => 2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) (Icc 0 B)).mul
      (hp.continuousOn.comp (by unfold parabolicPoint; fun_prop)
        (fun b hb => translated_upper_parabola_mem_disk hY hb hheight hδ))
  have hIm : IntervalIntegrable (fun b : ℝ => (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) *
      f (δ + parabolicPoint a b)) volume (-B) 0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith : -B ≤ 0)
    exact (by fun_prop : ContinuousOn (fun b : ℝ => 2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) (Icc (-B) 0)).mul
      (hm.continuousOn.comp (by unfold parabolicPoint; fun_prop)
        (fun b hb => translated_lower_parabola_mem_disk hY hb hheight hδ))
  have hIv (c : ℂ) (hf : DifferentiableOn ℂ f (ball c R)) {s t : ℝ}
      (hs : δ + ((a ^ 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I ∈ ball c R)
      (ht : δ + ((a ^ 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ∈ ball c R) :
      IntervalIntegrable (fun y : ℝ => Complex.I * f (δ + ((a ^ 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) volume s t := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (hf.continuousOn.comp (by fun_prop)
      (fun y hy => affine_line_mem_of_endpoints (convex_ball c R) _ _ hs ht hy))
  have hvp := hIv cp hp (s := 0) (t := 2 * a * B)
    (by simpa only [Complex.ofReal_zero, zero_mul, add_zero, ← hP0] using h0p) (by rwa [← hCp])
  have hvm := hIv cm hm (s := -(2 * a * B)) (t := 0)
    (by simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, ← hCm] using hcm)
    (by simpa only [Complex.ofReal_zero, zero_mul, add_zero, ← hP0] using h0m)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hIm hIp
  have hvsplit := intervalIntegral.integral_add_adjacent_intervals hvm hvp
  have hupper := upper_parabolic_integral_eq_polygon ha hB hY hheight hδ hp
  have hlower := lower_parabolic_integral_eq_polygon ha hB hY hheight hδ hm
  rw [segmentIntegral_reverse hp hpp hcp] at hupper
  change _ = Neuschel.segmentIntegral f P0 Cp + -Neuschel.segmentIntegral f Pp Cp at hupper
  change _ = Neuschel.segmentIntegral f Pm Cm + Neuschel.segmentIntegral f Cm P0 at hlower
  change (∫ b in (-B)..B, _) = _
  linear_combination -hsplit + hlower + hupper - hHm - hVm - hVp + hHp + hvsplit

/-- Exact equality of the full shifted Hankel integral and the parabolic
arc with its two infinite horizontal tails. -/
theorem shifted_hankel_eq_parabolic_with_tails {a B Y d : ℝ} {δ : ℂ}
    (ha : 0 < a) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) {f : ℂ → ℂ}
    (hp : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2))))
    (hm : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2))))
    (hlo : IntegrableOn (fun u : ℝ => f (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I)) (Iic (a ^ 2)))
    (hhi : IntegrableOn (fun u : ℝ => f (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I)) (Iic (a ^ 2))) :
    shiftedHankelIntegral (a ^ 2) (2 * a * B) δ f =
      (∫ u in Iic (a ^ 2 - B ^ 2), f (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I)) +
        parabolicArcIntegral a B δ f -
      (∫ u in Iic (a ^ 2 - B ^ 2), f (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I)) := by
  have hsub : Iic (a ^ 2 - B ^ 2) ⊆ Iic (a ^ 2) := Iic_subset_Iic.mpr (by nlinarith [sq_nonneg B])
  have hl := intervalIntegral.integral_Iic_sub_Iic (hlo.mono_set hsub) hlo
  have hh := intervalIntegral.integral_Iic_sub_Iic (hhi.mono_set hsub) hhi
  have hp := finite_parabolic_integral_eq_polygon ha hB hY hheight hδ hp hm
  dsimp only [shiftedHankelIntegral]
  linear_combination hl - hh - hp

end ThisWork.HigherRank
