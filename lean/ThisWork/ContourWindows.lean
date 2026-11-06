module

public import ThisWork.HankelTruncation

/-! Exact extraction of the saddle window on each oriented contour edge. -/

@[expose] public section

namespace ThisWork

open Set MeasureTheory

noncomputable def contourWindow (j : Branch) (σ : ℂ) (a b right height : ℝ) (f : ℂ → ℂ) : ℂ :=
  match j with
  | .one => ∫ u in σ.re - a..σ.re + b, f ((u : ℂ) - (height : ℂ) * Complex.I)
  | .two => -(∫ u in σ.re - a..σ.re + b, f ((u : ℂ) + (height : ℂ) * Complex.I))
  | .three => ∫ v in σ.im - a..σ.im + b, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)

theorem finiteHankelIntegral_sub_lower_window {left right height a b : ℝ} {σ : ℂ} {f : ℂ → ℂ}
    (hleft : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) - (height : ℂ) * Complex.I)) volume left (σ.re - a))
    (hwindow : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) - (height : ℂ) * Complex.I)) volume (σ.re - a) (σ.re + b))
    (hright : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) - (height : ℂ) * Complex.I)) volume (σ.re + b) right) :
    finiteHankelIntegral left right height f - contourWindow .one σ a b right height f =
      (∫ u in left..σ.re - a, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      (∫ u in σ.re + b..right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
      ∫ u in left..right, f ((u : ℂ) + (height : ℂ) * Complex.I) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals hleft hwindow
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hwindow) hright
  simp only [finiteHankelIntegral, contourWindow]
  rw [← h2, ← h1]
  ring

theorem finiteHankelIntegral_sub_upper_window {left right height a b : ℝ} {σ : ℂ} {f : ℂ → ℂ}
    (hleft : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (height : ℂ) * Complex.I)) volume left (σ.re - a))
    (hwindow : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (height : ℂ) * Complex.I)) volume (σ.re - a) (σ.re + b))
    (hright : IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (height : ℂ) * Complex.I)) volume (σ.re + b) right) :
    finiteHankelIntegral left right height f - contourWindow .two σ a b right height f =
      (∫ u in left..right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      (∫ v in -height..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
      (∫ u in left..σ.re - a, f ((u : ℂ) + (height : ℂ) * Complex.I)) -
      ∫ u in σ.re + b..right, f ((u : ℂ) + (height : ℂ) * Complex.I) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals hleft hwindow
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hwindow) hright
  simp only [finiteHankelIntegral, contourWindow]
  rw [← h2, ← h1]
  ring

theorem finiteHankelIntegral_sub_vertical_window {left right height a b : ℝ} {σ : ℂ} {f : ℂ → ℂ}
    (hlower : IntervalIntegrable (fun v : ℝ => Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) volume (-height) (σ.im - a))
    (hwindow : IntervalIntegrable (fun v : ℝ => Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) volume (σ.im - a) (σ.im + b))
    (hupper : IntervalIntegrable (fun v : ℝ => Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) volume (σ.im + b) height) :
    finiteHankelIntegral left right height f - contourWindow .three σ a b right height f =
      (∫ u in left..right, f ((u : ℂ) - (height : ℂ) * Complex.I)) +
      (∫ v in -height..σ.im - a, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) +
      (∫ v in σ.im + b..height, Complex.I * f ((right : ℂ) + (v : ℂ) * Complex.I)) -
      ∫ u in left..right, f ((u : ℂ) + (height : ℂ) * Complex.I) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals hlower hwindow
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hlower.trans hwindow) hupper
  simp only [finiteHankelIntegral, contourWindow]
  rw [← h2, ← h1]
  ring

end ThisWork
