module
public import ThisWork.HankelDeformation
/-! Quantitative horizontal contour displacement inside a holomorphic rectangle. -/
public section
namespace ThisWork.Analytic
open Set MeasureTheory

theorem norm_horizontal_rectangle_sub_le {f : ℂ → ℂ} {U : Set ℂ} {a b A B E : ℝ}
    (hf : DifferentiableOn ℂ f U)
    (hrect : ∀ z : ℂ, z.re ∈ uIcc a b → z.im ∈ uIcc A B → z ∈ U)
    (ha : ∀ v ∈ uIcc A B, ‖f ((a : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E)
    (hb : ∀ v ∈ uIcc A B, ‖f ((b : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E) :
    ‖(∫ u in a..b, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
        ∫ u in a..b, f ((u : ℂ) + (B : ℂ) * Complex.I)‖ ≤ 2 * E * |B - A| := by
  have hi := rectangle_integral_identity hf hrect
  have hbound (r : ℝ) (hr : ∀ v ∈ uIcc A B, ‖f ((r : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E) :
      ‖∫ v in A..B, Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E * |B - A| := by
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun v hv => by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact hr v (uIoc_subset_uIcc hv))
  have he : (∫ u in a..b, f ((u : ℂ) + (A : ℂ) * Complex.I)) -
      (∫ u in a..b, f ((u : ℂ) + (B : ℂ) * Complex.I)) =
      (∫ v in A..B, Complex.I * f ((a : ℂ) + (v : ℂ) * Complex.I)) -
      (∫ v in A..B, Complex.I * f ((b : ℂ) + (v : ℂ) * Complex.I)) := by linear_combination hi
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add (hbound a ha) (hbound b hb)).trans_eq (by ring))

end ThisWork.Analytic
