module
public import ThisWork.ContourWindows
/-! A reusable finite polygonal-contour estimate away from a lower-edge window. -/
public section
namespace ThisWork.Analytic
open Set MeasureTheory

theorem norm_finiteHankel_sub_lowerWindow_le {left right height a b E : ℝ} {σ : ℂ} {f : ℂ → ℂ}
    (hh : 0 ≤ height) (ha : 0 ≤ a) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (hl : left ≤ σ.re - a) (hr : σ.re + b ≤ right)
    (hc : ContinuousOn f (hankelTrace right height))
    (hlo : ∀ u ∈ Icc left (σ.re - a), ‖f ((u : ℂ) - (height : ℂ) * Complex.I)‖ ≤ E)
    (hro : ∀ u ∈ Icc (σ.re + b) right, ‖f ((u : ℂ) - (height : ℂ) * Complex.I)‖ ≤ E)
    (hu : ∀ u ∈ Icc left right, ‖f ((u : ℂ) + (height : ℂ) * Complex.I)‖ ≤ E)
    (hv : ∀ v ∈ Icc (-height) height, ‖f ((right : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E) :
    ‖finiteHankelIntegral left right height f - contourWindow .one σ a b right height f‖ ≤
      (2 * (right - left) + 2 * height) * E := by
  have hw : σ.re - a ≤ σ.re + b := by linarith
  have hcL : ContinuousOn (fun u : ℝ => f ((u : ℂ) - (height : ℂ) * Complex.I)) (Icc left right) := by
    apply hc.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) - (height : ℂ) * Complex.I)).continuousOn
    intro u hu
    apply Or.inl
    apply Or.inl
    exact ⟨u, hu.2, by simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]⟩
  have hcl := hcL.mono (Icc_subset_Icc le_rfl (by linarith : σ.re - a ≤ right))
  have hcw := hcL.mono (Icc_subset_Icc hl hr)
  have hcr := hcL.mono (Icc_subset_Icc (by linarith : left ≤ σ.re + b) le_rfl)
  rw [finiteHankelIntegral_sub_lower_window
    (hcl.intervalIntegrable_of_Icc hl) (hcw.intervalIntegrable_of_Icc hw) (hcr.intervalIntegrable_of_Icc hr)]
  have h₁ : ‖∫ u in left..σ.re - a, f ((u : ℂ) - (height : ℂ) * Complex.I)‖ ≤
      E * (σ.re - a - left) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := left) (b := σ.re - a) (fun u hu => hlo u
      ((uIoc_subset_uIcc hu) |> fun h => by simpa only [uIcc_of_le hl] using h))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hl)] using h
  have h₂ : ‖∫ u in σ.re + b..right, f ((u : ℂ) - (height : ℂ) * Complex.I)‖ ≤
      E * (right - (σ.re + b)) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ.re + b) (b := right) (fun u hu => hro u
      ((uIoc_subset_uIcc hu) |> fun h => by simpa only [uIcc_of_le hr] using h))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hr)] using h
  have h₃ : ‖∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      E * (2 * height) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -height) (b := height)
      (f := fun v : ℝ => Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) (fun v hv' => by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact hv v (by simpa only [uIcc_of_le (by linarith : -height ≤ height)] using uIoc_subset_uIcc hv'))
    convert h using 1
    rw [abs_of_nonneg (by linarith : 0 ≤ height - -height)]
    ring
  have hlr : left ≤ right := by linarith
  have h₄ : ‖∫ u in left..right, f ((u : ℂ) + (height : ℂ) * Complex.I)‖ ≤ E * (right - left) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := left) (b := right) (fun u hu' => hu u
      (by simpa only [uIcc_of_le hlr] using uIoc_subset_uIcc hu'))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hlr)] using h
  have htri := norm_sub_le
    ((∫ u in left..σ.re - a, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      (∫ u in σ.re + b..right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      ∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I))
    (∫ u in left..right, f ((u : ℂ) + (height : ℂ) * Complex.I))
  have hsum := (norm_add_le
    ((∫ u in left..σ.re - a, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      ∫ u in σ.re + b..right, f ((u : ℂ) - (height : ℂ) * Complex.I))
    (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I))).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)
  exact htri.trans ((add_le_add hsum h₄).trans (by nlinarith))

end ThisWork.Analytic
