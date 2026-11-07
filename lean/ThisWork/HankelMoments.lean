module

public import ThisWork.Argument
public import ThisWork.HankelLinearity
public import ThisWork.MomentIndependence

/-! The exact change from the original polynomial weights to scaled power moments. -/

public section

namespace ThisWork.Analytic


open Set MeasureTheory

private theorem second_moment_integrand (a : ℂ) (f : ℂ → ℂ) :
    (fun x => x ^ 2 * f x) =
      (fun x => (a ^ 2 * f x - (2 * a) * ((a - x) * f x)) + (a - x) ^ 2 * f x) := by
  funext x
  ring

theorem HankelIntegrable.first_moment {r h : ℝ} {f : ℂ → ℂ} (a : ℂ)
    (h0 : HankelIntegrable r h f)
    (h1 : HankelIntegrable r h (fun x => (a - x) * f x)) :
    HankelIntegrable r h (fun x => x * f x) := by
  simpa only [sub_mul, sub_sub_cancel] using (h0.const_mul a).sub h1

theorem HankelIntegrable.second_moment {r h : ℝ} {f : ℂ → ℂ} (a : ℂ)
    (h0 : HankelIntegrable r h f)
    (h1 : HankelIntegrable r h (fun x => (a - x) * f x))
    (h2 : HankelIntegrable r h (fun x => (a - x) ^ 2 * f x)) :
    HankelIntegrable r h (fun x => x ^ 2 * f x) := by
  rw [second_moment_integrand a f]
  exact ((h0.const_mul (a ^ 2)).sub (h1.const_mul (2 * a))).add h2

theorem hankelIntegral_first_moment {r h : ℝ} {f : ℂ → ℂ} (a : ℂ)
    (h0 : HankelIntegrable r h f)
    (h1 : HankelIntegrable r h (fun x => (a - x) * f x)) :
    hankelIntegral r h (fun x => x * f x) =
      a * hankelIntegral r h f - hankelIntegral r h (fun x => (a - x) * f x) := by
  simpa only [sub_mul, sub_sub_cancel, hankelIntegral_const_mul] using
    hankelIntegral_sub (h0.const_mul a) h1

theorem hankelIntegral_second_moment {r h : ℝ} {f : ℂ → ℂ} (a : ℂ)
    (h0 : HankelIntegrable r h f)
    (h1 : HankelIntegrable r h (fun x => (a - x) * f x))
    (h2 : HankelIntegrable r h (fun x => (a - x) ^ 2 * f x)) :
    hankelIntegral r h (fun x => x ^ 2 * f x) =
      a ^ 2 * hankelIntegral r h f - 2 * a * hankelIntegral r h (fun x => (a - x) * f x) +
        hankelIntegral r h (fun x => (a - x) ^ 2 * f x) := by
  rw [second_moment_integrand a f,
    hankelIntegral_add ((h0.const_mul (a ^ 2)).sub (h1.const_mul (2 * a))) h2,
    hankelIntegral_sub (h0.const_mul (a ^ 2)) (h1.const_mul (2 * a)),
    hankelIntegral_const_mul, hankelIntegral_const_mul]

theorem HankelIntegrable.scaled_power {r h : ℝ} {f : ℂ → ℂ} (R : ℝ) (k : ℕ)
    (hf : HankelIntegrable r h (fun x => x ^ k * f x)) :
    HankelIntegrable r h (fun x => (x / (R : ℂ)) ^ k * f x) := by
  simpa only [div_eq_mul_inv, mul_pow, inv_pow, mul_left_comm, mul_assoc] using
    hf.const_mul ((R : ℂ) ^ k)⁻¹

theorem hankelIntegral_scaled_power (r h R : ℝ) (f : ℂ → ℂ) (k : ℕ) :
    hankelIntegral r h (fun x => (x / (R : ℂ)) ^ k * f x) =
      ((R : ℂ) ^ k)⁻¹ * hankelIntegral r h (fun x => x ^ k * f x) := by
  simpa only [div_eq_mul_inv, mul_pow, inv_pow, mul_left_comm, mul_assoc] using
    hankelIntegral_const_mul r h (fun x => x ^ k * f x) ((R : ℂ) ^ k)⁻¹

theorem momentTransform_hankel {r h R : ℝ} {f : ℂ → ℂ} (n : ℕ) (c : ℂ)
    (h0 : HankelIntegrable r h f)
    (h1 : HankelIntegrable r h (fun x => ((n : ℂ) - x) * f x))
    (h2 : HankelIntegrable r h (fun x => ((n : ℂ) - x) ^ 2 * f x)) :
    momentTransform n R
        (fun k : Fin 3 => c * hankelIntegral r h (fun x => ((n : ℂ) - x) ^ k.val * f x)) =
      (fun k : Fin 3 => c * hankelIntegral r h (fun x => (x / (R : ℂ)) ^ k.val * f x)) := by
  ext k
  fin_cases k
  · simp [momentTransform]
  · simp [momentTransform]
    have hs := hankelIntegral_scaled_power r h R f 1
    simp only [pow_one] at hs
    rw [hs, hankelIntegral_first_moment (n : ℂ) h0 h1]
    ring
  · simp [momentTransform]
    rw [hankelIntegral_scaled_power, hankelIntegral_second_moment (n : ℂ) h0 h1 h2]
    ring

theorem branchIntegral_momentTransform_eq_contour [PositiveArgument] {α₁ α₂ r h R : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n : ℕ)
    (hr₀ : 0 < r) (hr : r < min (α₁ * n + 1) (α₂ * n + 1)) (hh : 1 ≤ h) :
    momentTransform n R (normalizedBranchIntegral α₁ α₂ j n) =
      (fun k : Fin 3 => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        hankelIntegral r h (fun x => (x / (R : ℂ)) ^ k.val * normalizedKernel α₁ α₂ j n x)) := by
  have he : normalizedBranchIntegral α₁ α₂ j n =
      (fun k : Fin 3 => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        hankelIntegral r h (fun x => ((n : ℂ) - x) ^ k.val * normalizedKernel α₁ α₂ j n x)) :=
    funext (fun k => branchIntegral_eq_deformed h₁ h₂ j n k hr₀ hr hh)
  rw [he]
  have h0 : HankelIntegrable r h (normalizedKernel α₁ α₂ j n) := by
    simpa only [HankelIntegrable, pow_zero, one_mul] using
      weighted_hankel_absolutely_convergent h₁ h₂ j n 0 hr₀ hr hh
  have h1 : HankelIntegrable r h (fun x => ((n : ℂ) - x) * normalizedKernel α₁ α₂ j n x) := by
    simpa only [HankelIntegrable, pow_one] using
      weighted_hankel_absolutely_convergent h₁ h₂ j n 1 hr₀ hr hh
  exact momentTransform_hankel n _ h0 h1
    (weighted_hankel_absolutely_convergent h₁ h₂ j n 2 hr₀ hr hh)

theorem branchIntegral_momentTransform_eq_scaled_contour [PositiveArgument] {α₁ α₂ r h R : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (n : ℕ) (hR : 0 < R)
    (hr₀ : 0 < r) (hr : R * r < min (α₁ * n + 1) (α₂ * n + 1)) (hh : 1 ≤ R * h) :
    momentTransform n R (normalizedBranchIntegral α₁ α₂ j n) =
      (fun k : Fin 3 => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (R : ℂ) *
        hankelIntegral r h (fun s => s ^ k.val * normalizedKernel α₁ α₂ j n ((R : ℂ) * s))) := by
  rw [branchIntegral_momentTransform_eq_contour h₁ h₂ j n (mul_pos hR hr₀) hr hh]
  ext k
  rw [hankelIntegral_scale _ r h hR]
  simp only [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne'), mul_assoc]

end ThisWork.Analytic
