module
public import ThisWork.Trajectory.GrowingMoments
public import ThisWork.Trajectory.SqrtOriginalMoments
/-! Growing Gaussian moments in the original three integral coordinates. -/
@[expose] public section
namespace ThisWork.Trajectory.ReflectedSaddleData
open Set Filter Metric Analytic
open scoped Topology
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
    (G : GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius)

noncomputable def normalizingScalar (n : ℕ) : ℂ :=
  F.gaussianNormalizer n / (F.growingSaddleKernel n * cauchyFactor * (sqrtScale (F.index n) : ℂ))

theorem eventually_normalizingScalar_ne_zero : ∀ᶠ n : ℕ in atTop, F.normalizingScalar n ≠ 0 := by
  filter_upwards [F.eventually_growingSaddleKernel_ne_zero,
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
        (branchIntegral m d A₁ A₂ z .one (F.index n)) k = F.normalizedFullMoment G n k.val := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  filter_upwards [F.index_tendsto.eventually (eventually_right_factor_conditions F.A₁_pos c),
    F.index_tendsto.eventually (eventually_right_factor_conditions F.A₂_pos c),
    (sqrtScale_tendsto.comp F.index_tendsto).eventually (eventually_ge_atTop (1 / G.height)),
    F.index_tendsto.eventually (eventually_gt_atTop (0 : ℕ))] with n hA₁ hA₂ hh hn
  have hu : sqrtScale (F.index n) * c < min (A₁ * F.index n + 1) (A₂ * F.index n + 1) :=
    lt_min (by linarith [hA₁.1, hA₁.2]) (by linarith [hA₂.1, hA₂.2])
  have hh' : 1 ≤ sqrtScale (F.index n) * G.height := (div_le_iff₀ G.height_pos).mp hh
  have hv := congrFun (branchIntegral_momentTransform_eq_scaled_contour F.z_pos F.A₁_pos F.A₂_pos
    m d .one (F.index n) (sqrtScale_pos hn) hc hu hh') k
  change momentTransform (m * F.index n) (sqrtScale (F.index n))
    (branchIntegral m d A₁ A₂ z .one (F.index n)) k = cauchyFactor * (sqrtScale (F.index n) : ℂ) * F.fullMoment G n k.val at hv
  rw [hv, normalizingScalar, mul_assoc (F.growingSaddleKernel n) cauchyFactor (sqrtScale (F.index n) : ℂ)]
  exact div_mul_cancel_extra_factor _ _ _ _
    (mul_ne_zero cauchyFactor_ne_zero (Complex.ofReal_ne_zero.mpr (sqrtScale_pos hn).ne'))

theorem normalized_originalMoment_tendsto (k : Fin 3) :
    Tendsto (fun n => F.normalizingScalar n * momentTransform (m * F.index n) (sqrtScale (F.index n))
      (branchIntegral m d A₁ A₂ z .one (F.index n)) k) atTop
      (𝓝 ((-(doubleSaddleScale d A₁ A₂ z : ℂ)) ^ k.val)) := by
  obtain ⟨G⟩ := F.exists_contourChoice
  exact (F.normalizedFullMoment_tendsto G k.val).congr'
    ((F.eventually_normalized_transform_eq_fullMoment G k).mono (fun _ hn => hn.symm))

end ThisWork.Trajectory.ReflectedSaddleData
