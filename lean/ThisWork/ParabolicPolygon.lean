module

public import ThisWork.ParabolicDeformation
public import ThisWork.ContourSegments

/-! Exact polygonal replacements of the two finite parabolic half-arcs. -/

@[expose] public section
namespace ThisWork

open Set Metric MeasureTheory

noncomputable def parabolicCorner (a B : ℝ) : ℂ :=
  ((a ^ 2 : ℝ) : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I

theorem norm_parabolicCorner_sub_upper_center_le {a B Y : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (_hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ‖parabolicCorner a B - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ Y := by
  have hprod : 0 ≤ 4 * a * (Y - a * B) := by nlinarith [pow_nonneg hB 3]
  have habY : a * B ≤ Y := by nlinarith
  rw [show parabolicCorner a B - (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) =
    ((2 * a * B - Y : ℝ) : ℂ) * Complex.I by dsimp only [parabolicCorner]; push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith, by linarith⟩

theorem translated_mem_parabolic_disk {x c δ : ℂ} {Y d : ℝ}
    (hx : ‖x - c‖ ≤ Y) (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) :
    δ + x ∈ ball c (Real.sqrt (Y ^ 2 + d ^ 2)) := by
  rw [mem_ball, dist_eq_norm]
  calc
    _ = ‖δ + (x - c)‖ := by congr 1; abel
    _ ≤ ‖δ‖ + ‖x - c‖ := norm_add_le _ _
    _ < _ := by linarith

theorem upper_parabolic_integral_eq_polygon {a B Y d : ℝ} {δ : ℂ}
    (ha : 0 < a) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)))) :
    (∫ b in (0 : ℝ)..B, (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) *
      f (δ + parabolicPoint a b)) =
      Neuschel.segmentIntegral f (δ + parabolicPoint a 0) (δ + parabolicCorner a B) +
        Neuschel.segmentIntegral f (δ + parabolicCorner a B) (δ + parabolicPoint a B) := by
  rw [upper_parabolic_integral_eq_segment hB hY hheight hδ hf]
  exact (segmentIntegral_add hf
    (translated_upper_parabola_mem_disk hY ⟨le_rfl, hB⟩ hheight hδ)
    (translated_mem_parabolic_disk (norm_parabolicCorner_sub_upper_center_le ha hB hY hheight) hδ)
    (translated_upper_parabola_mem_disk hY ⟨hB, le_rfl⟩ hheight hδ)).symm

theorem norm_parabolicCorner_sub_lower_center_le {a B Y : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ‖parabolicCorner a (-B) - (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I)‖ ≤ Y := by
  have hc : starRingEnd ℂ (parabolicCorner a B -
      (((a ^ 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)) =
      parabolicCorner a (-B) - (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) := by
    simp only [parabolicCorner, map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [← hc, Complex.norm_conj]
  exact norm_parabolicCorner_sub_upper_center_le ha hB hY hheight

theorem lower_parabolic_integral_eq_polygon {a B Y d : ℝ} {δ : ℂ}
    (ha : 0 < a) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y)
    (hδ : ‖δ‖ < Real.sqrt (Y ^ 2 + d ^ 2) - Y) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f
      (ball (((a ^ 2 : ℝ) : ℂ) - (Y : ℂ) * Complex.I) (Real.sqrt (Y ^ 2 + d ^ 2)))) :
    (∫ b in (-B)..(0 : ℝ), (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) *
      f (δ + parabolicPoint a b)) =
      Neuschel.segmentIntegral f (δ + parabolicPoint a (-B)) (δ + parabolicCorner a (-B)) +
        Neuschel.segmentIntegral f (δ + parabolicCorner a (-B)) (δ + parabolicPoint a 0) := by
  rw [lower_parabolic_integral_eq_segment hB hY hheight hδ hf]
  exact (segmentIntegral_add hf
    (translated_lower_parabola_mem_disk hY ⟨le_rfl, by linarith⟩ hheight hδ)
    (translated_mem_parabolic_disk (norm_parabolicCorner_sub_lower_center_le ha hB hY hheight) hδ)
    (translated_lower_parabola_mem_disk hY ⟨by linarith, le_rfl⟩ hheight hδ)).symm

end ThisWork
