module
public import ThisWork.Trajectory.SqrtKernelNorm
public import ThisWork.OriginalMomentLimits
public import ThisWork.Trajectory.Contours
/-! Returning the square-root power moments to the original integral coordinates. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology OnePoint

theorem branchIntegral_momentTransform_eq_scaled_contour {A₁ A₂ z r h R : ℝ}
    (hz : 0 < z) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (m d : ℕ) (j : Branch) (n : ℕ)
    (hR : 0 < R) (hr₀ : 0 < r) (hr : R * r < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ R * h) :
    momentTransform (m * n) R (branchIntegral m d A₁ A₂ z j n) =
      (fun k : Fin 3 => cauchyFactor * (R : ℂ) *
        hankelIntegral r h (fun s => s ^ k.val * kernel m d A₁ A₂ z j n ((R : ℂ) * s))) := by
  have he : branchIntegral m d A₁ A₂ z j n =
      (fun k : Fin 3 => cauchyFactor * hankelIntegral (R * r) (R * h)
        (fun x => ((m * n : ℕ) : ℂ) - x |> fun y => y ^ k.val * kernel m d A₁ A₂ z j n x)) := by
    funext k
    simpa only [Nat.cast_mul, cauchyFactor] using branchIntegral_eq_deformed hz h₁ h₂ m d j n k (mul_pos hR hr₀) hr hh
  rw [he]
  have h0 : HankelIntegrable (R * r) (R * h) (kernel m d A₁ A₂ z j n) := by
    simpa only [pow_zero, one_mul] using weighted_hankel_integrable hz h₁ h₂ m d j n 0 (mul_pos hR hr₀) hr hh
  have h1 : HankelIntegrable (R * r) (R * h)
      (fun x => ((m * n : ℕ) : ℂ) - x |> fun y => y * kernel m d A₁ A₂ z j n x) := by
    simpa only [pow_one, Nat.cast_mul] using weighted_hankel_integrable hz h₁ h₂ m d j n 1 (mul_pos hR hr₀) hr hh
  have h2 : HankelIntegrable (R * r) (R * h)
      (fun x => (((m * n : ℕ) : ℂ) - x) ^ 2 * kernel m d A₁ A₂ z j n x) := by
    simpa only [Nat.cast_mul] using weighted_hankel_integrable hz h₁ h₂ m d j n 2 (mul_pos hR hr₀) hr hh
  rw [momentTransform_hankel (m * n) cauchyFactor h0 h1 h2]
  funext k
  rw [hankelIntegral_scale _ r h hR]
  simp only [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne'), mul_assoc]

namespace CanonicalSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : CanonicalSaddleData m d A₁ A₂ z)

noncomputable def normalizingScalar (n : ℕ) : ℂ :=
  F.gaussianNormalizer n / (F.saddleKernel n * cauchyFactor * (sqrtScale (F.index n) : ℂ))

theorem eventually_normalizingScalar_ne_zero : ∀ᶠ n : ℕ in atTop, F.normalizingScalar n ≠ 0 := by
  filter_upwards [F.eventually_saddleKernel_ne_zero,
    F.index_tendsto.eventually (eventually_gt_atTop (0 : ℕ))] with n hK hn
  have hR := sqrtScale_pos hn
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  exact div_ne_zero
    (mul_ne_zero (Neuschel.leadingRoot_ne_zero 2 F.data.velocity_ne_zero _)
      (Complex.ofReal_ne_zero.mpr (div_pos (Real.rpow_pos_of_pos hR _) hG).ne'))
    (mul_ne_zero (mul_ne_zero hK cauchyFactor_ne_zero) (Complex.ofReal_ne_zero.mpr hR.ne'))

theorem eventually_normalized_transform_eq_fullMoment (k : Fin 3) :
    ∀ᶠ n : ℕ in atTop,
      F.normalizingScalar n * momentTransform (m * F.index n) (sqrtScale (F.index n))
        (branchIntegral m d A₁ A₂ z .three (F.index n)) k = F.normalizedFullMoment n k.val := by
  have hc := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  filter_upwards [F.index_tendsto.eventually (eventually_sqrtDisk_mapsTo_kernelDomain F.A₁_pos F.A₂_pos hc),
    (sqrtScale_tendsto.comp F.index_tendsto).eventually (eventually_ge_atTop (1 / doubleSaddleScale d A₁ A₂ z))]
    with n hn hh
  have hr := saddleContourRight_bounds hc .three (F.center_mem n)
  have hupper := (hn.2 (F.center_mem n)).2
  change ((sqrtScale (F.index n) : ℂ) * F.center n).re <
    min (A₁ * F.index n + 1) (A₂ * F.index n + 1) at hupper
  have hupper' : sqrtScale (F.index n) * saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three (F.center n) <
      min (A₁ * F.index n + 1) (A₂ * F.index n + 1) := by
    simpa only [saddleContourRight, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hupper
  have hh' : 1 ≤ sqrtScale (F.index n) * saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three (F.center n) := by
    change 1 ≤ sqrtScale (F.index n) * doubleSaddleScale d A₁ A₂ z
    exact (div_le_iff₀ hc).mp hh
  have hv := congrFun (branchIntegral_momentTransform_eq_scaled_contour F.z_pos F.A₁_pos F.A₂_pos
    m d .three (F.index n) (sqrtScale_pos hn.1) hr.1 hupper' hh') k
  change momentTransform (m * F.index n) (sqrtScale (F.index n))
    (branchIntegral m d A₁ A₂ z .three (F.index n)) k = cauchyFactor * (sqrtScale (F.index n) : ℂ) * F.fullMoment n k.val at hv
  rw [hv, normalizingScalar, mul_assoc (F.saddleKernel n) cauchyFactor (sqrtScale (F.index n) : ℂ)]
  exact div_mul_cancel_extra_factor _ _ _ _
    (mul_ne_zero cauchyFactor_ne_zero (Complex.ofReal_ne_zero.mpr (sqrtScale_pos hn.1).ne'))

theorem normalized_originalMoment_tendsto (k : Fin 3) :
    Tendsto (fun n => F.normalizingScalar n * momentTransform (m * F.index n) (sqrtScale (F.index n))
      (branchIntegral m d A₁ A₂ z .three (F.index n)) k) atTop
      (𝓝 ((doubleSaddleScale d A₁ A₂ z : ℂ) ^ k.val)) :=
  (F.normalizedFullMoment_tendsto k.val).congr'
    ((F.eventually_normalized_transform_eq_fullMoment k).mono (fun _ hn => hn.symm))

end CanonicalSaddleData
end ThisWork.Trajectory
