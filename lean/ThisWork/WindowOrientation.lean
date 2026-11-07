module

public import ThisWork.Argument
public import ThisWork.LocalWindowIdentity
public import ThisWork.SaddleContours

/-! Orientation and position of the three actual local contour windows. -/

@[expose] public section

namespace ThisWork.Analytic


open Set MeasureTheory Filter
open scoped Topology OnePoint

noncomputable def branchOrientation : Branch → ℂ
  | .one | .three => 1
  | .two => -1

@[simp] theorem norm_branchOrientation (j : Branch) : ‖branchOrientation j‖ = 1 := by
  cases j <;> simp [branchOrientation]

theorem branchOrientation_ne_zero (j : Branch) : branchOrientation j ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_branchOrientation]; norm_num)

theorem horizontal_window_shift (f : ℂ → ℂ) (σ : ℂ) (a b y : ℝ) (hy : σ.im = y) :
    (∫ u in σ.re - a..σ.re + b, f ((u : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ t in -a..b, f ((t : ℂ) + σ) := by
  have hs := intervalIntegral.integral_comp_add_right
    (fun u : ℝ => f ((u : ℂ) + (y : ℂ) * Complex.I)) σ.re (a := -a) (b := b)
  rw [show -a + σ.re = σ.re - a by ring, add_comm b σ.re] at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg f
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hy]

theorem vertical_window_shift (f : ℂ → ℂ) (σ : ℂ) (a b : ℝ) :
    (∫ v in σ.im - a..σ.im + b, Complex.I * f ((σ.re : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ t in -a..b, Complex.I * f ((t : ℂ) * Complex.I + σ) := by
  have hs := intervalIntegral.integral_comp_add_right
    (fun v : ℝ => Complex.I * f ((σ.re : ℂ) + (v : ℂ) * Complex.I)) σ.im (a := -a) (b := b)
  rw [show -a + σ.im = σ.im - a by ring, add_comm b σ.im] at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg (fun z : ℂ => Complex.I * f z)
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, add_comm]

theorem saddleDisk_im_side {c : ℝ} (hc : 0 < c) (j : Branch) {σ : ℂ}
    (hσ : σ ∈ saddleDisk c j) :
    match j with
    | .one => σ.im ≤ -(c / 4)
    | .two => c / 4 ≤ σ.im
    | .three => |σ.im| ≤ c / 4 := by
  have hd : ‖σ - (c : ℂ) * rho j‖ ≤ c / 4 := by
    simpa only [saddleDisk, Metric.mem_closedBall, dist_eq_norm] using hσ
  have hi := (Complex.abs_im_le_norm (σ - (c : ℂ) * rho j)).trans hd
  have hsqrt : 1 ≤ Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num)
  have hm := mul_le_mul_of_nonneg_right hsqrt hc.le
  cases j <;> simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, rho_one_im, rho_two_im, rho_three, Complex.one_im, mul_zero, sub_zero] at hi ⊢
  · nlinarith [(abs_le.mp hi).2]
  · nlinarith [(abs_le.mp hi).1]
  · exact hi

theorem contourWindow_eq_ray_window {c : ℝ} (hc : 0 < c) (j : Branch) {σ : ℂ}
    (hσ : σ ∈ saddleDisk c j) (a b : ℝ) (f : ℂ → ℂ) :
    contourWindow j σ a b (saddleContourRight c j σ) (saddleContourHeight c j σ) f =
      branchOrientation j * ∫ t in -a..b, saddleTangent j * f ((t : ℂ) * saddleTangent j + σ) := by
  have hside := saddleDisk_im_side hc j hσ
  cases j
  · have hi : σ.im ≤ 0 := by change σ.im ≤ -(c / 4) at hside; linarith
    have he : σ.im = -|σ.im| := by rw [abs_of_nonpos hi, neg_neg]
    simpa only [contourWindow, saddleContourRight, saddleContourHeight, branchOrientation,
      saddleTangent, mul_one, one_mul, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      horizontal_window_shift f σ a b (-|σ.im|) he
  · have hi : 0 ≤ σ.im := by change c / 4 ≤ σ.im at hside; linarith
    have he : σ.im = |σ.im| := (abs_of_nonneg hi).symm
    simpa only [contourWindow, saddleContourRight, saddleContourHeight, branchOrientation,
      saddleTangent, mul_one, one_mul, neg_one_mul] using
      congrArg Neg.neg (horizontal_window_shift f σ a b |σ.im| he)
  · simpa only [contourWindow, saddleContourRight, branchOrientation, saddleTangent, one_mul] using
      vertical_window_shift f σ a b

namespace CompactSaddleFamily.LocalSaddleData

theorem eventually_contourWindow_eq_phase [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      contourWindow j (S.saddle (m + D.shift)) D.leftWidth D.rightWidth
        (saddleContourRight (saddleScale α₁ α₂) j (S.saddle (m + D.shift)))
        (saddleContourHeight (saddleScale α₁ α₂) j (S.saddle (m + D.shift)))
        (fun s => s ^ k * normalizedKernel α₁ α₂ j (m + D.shift + S.firstIndex)
          ((largeScale (m + D.shift + S.firstIndex) : ℂ) * s)) =
      branchOrientation j * normalizedKernel α₁ α₂ j (m + D.shift + S.firstIndex)
        ((largeScale (m + D.shift + S.firstIndex) : ℂ) * S.saddle (m + D.shift)) *
        D.localMoment (largeScale (m + D.shift + S.firstIndex)) k m := by
  filter_upwards [D.eventually_localKernelMoment_eq_phase h₁ h₂ k,
    D.eventually_localKernelMoment_eq_rayWindow h₁ h₂ k] with m hp hw
  rw [contourWindow_eq_ray_window (saddleScale_pos h₁ h₂) j (S.saddle_mem_disk h₁ h₂ (m + D.shift)), ← hw, hp]
  simp only [mul_assoc]

end CompactSaddleFamily.LocalSaddleData

end ThisWork.Analytic
