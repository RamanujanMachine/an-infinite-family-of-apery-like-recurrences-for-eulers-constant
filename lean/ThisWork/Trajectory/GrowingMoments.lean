module
public import ThisWork.Trajectory.GrowingWindowReflection
public import ThisWork.FullMomentAsymptotics
/-! Gaussian asymptotics for the complete growing Mellin–Barnes contour. -/
@[expose] public section
namespace ThisWork.Trajectory.ReflectedSaddleData
open Set Filter Metric Analytic
open scoped Topology OnePoint
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
    (G : GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius)

noncomputable def fullMoment (n k : ℕ) : ℂ :=
  hankelIntegral (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k)
noncomputable def growingSaddleKernel (n : ℕ) : ℂ := reflectionMomentFactor 0 * F.saddleKernel n
noncomputable def normalizedFullMoment (n k : ℕ) : ℂ :=
  F.gaussianNormalizer n * (F.growingSaddleKernel n)⁻¹ * F.fullMoment G n k

theorem fullMoment_absolute_leading_error (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖F.fullMoment G n k - reflectionMomentFactor k * F.saddleKernel n *
        F.data.localMoment (sqrtScale (F.index n)) k n‖ ≤
        C * doubleScale m d A₁ A₂ z (F.index n) *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
  obtain ⟨Ct, hCt, ht⟩ := F.uniform_full_growing_lower_window_remainder G k
  obtain ⟨Cr, hCr, hr⟩ := F.uniform_growing_window_reflection G k
  obtain ⟨Cd, hCd, hd⟩ := F.uniform_reflected_window_deformation G k
  refine ⟨Ct + Cr + ‖reflectionMomentFactor k‖ * Cd, by positivity, ?_⟩
  filter_upwards [ht, hr, hd, F.eventually_windowMoment_eq_phase k] with n htn hrn hdn hw
  have hd' : ‖reflectionMomentFactor k * F.heightMoment n k G.height -
      reflectionMomentFactor k * F.windowMoment n k‖ ≤
      (‖reflectionMomentFactor k‖ * Cd) * doubleScale m d A₁ A₂ z (F.index n) *
        Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
    rw [← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_left hdn (norm_nonneg _)).trans_eq (by ring)
  have htri := norm_add_le
    (F.fullMoment G n k - reflectionMomentFactor k * F.heightMoment n k G.height)
    (reflectionMomentFactor k * F.heightMoment n k G.height - reflectionMomentFactor k * F.windowMoment n k)
  have hmid : ‖F.fullMoment G n k - reflectionMomentFactor k * F.heightMoment n k G.height‖ ≤
      Ct * doubleScale m d A₁ A₂ z (F.index n) * Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) +
      Cr * doubleScale m d A₁ A₂ z (F.index n) * Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
    have h := norm_add_le
      (F.fullMoment G n k - contourWindow .one (-F.center n) F.data.rightWidth F.data.leftWidth
        (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k))
      (contourWindow .one (-F.center n) F.data.rightWidth F.data.leftWidth
        (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
        reflectionMomentFactor k * F.heightMoment n k G.height)
    rw [sub_add_sub_cancel] at h
    exact h.trans (add_le_add htn hrn)
  rw [sub_add_sub_cancel, hw] at htri
  rw [hw] at hd'
  convert htri.trans (add_le_add hmid hd') using 1
  · simp only [mul_assoc]
  · ring

theorem saddleKernel_log_norm_estimate :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      |Real.log ‖F.saddleKernel n‖ - Real.log (doubleScale m d A₁ A₂ z (F.index n)) -
        2 * doubleSaddleScale d A₁ A₂ z * sqrtScale (F.index n)| ≤
        C * (1 + Real.log (sqrtScale (F.index n))) := by
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_reflected_kernel_near_saddle F.d_pos F.A₁_pos F.A₂_pos F.z_pos
    F.family.errorConstant_nonneg m
  refine ⟨C, hC, ?_⟩
  filter_upwards [F.index_tendsto.eventually hb] with n hn
  exact hn (F.center n) (F.family.saddle_mem_disk F.d_pos F.A₁_pos F.A₂_pos F.z_pos (n + F.data.shift))
    (F.family.displacement (n + F.data.shift))

theorem eventually_scale_exp_le_saddleKernel {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, doubleScale m d A₁ A₂ z (F.index n) *
      Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - ε) * sqrtScale (F.index n)) ≤ ‖F.saddleKernel n‖ := by
  obtain ⟨C, _, hk⟩ := F.saddleKernel_log_norm_estimate
  filter_upwards [hk, F.index_tendsto.eventually (eventually_const_log_sqrt_le C hε),
    F.eventually_saddleKernel_ne_zero, F.index_tendsto.eventually (eventually_gt_atTop (0 : ℕ))]
    with n hn he hK hn₀
  have hH := doubleScale_pos (m := m) F.d_pos hn₀ F.A₁_pos F.A₂_pos F.z_pos
  calc
    _ = Real.exp (Real.log (doubleScale m d A₁ A₂ z (F.index n)) +
        (2 * doubleSaddleScale d A₁ A₂ z - ε) * sqrtScale (F.index n)) := by
      rw [Real.exp_add, Real.exp_log hH]
    _ ≤ Real.exp (Real.log ‖F.saddleKernel n‖) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hn).1])
    _ = _ := Real.exp_log (norm_pos_iff.mpr hK)

theorem fullMoment_leading_error (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖F.fullMoment G n k - F.growingSaddleKernel n *
        ((-1 : ℂ) ^ k * F.data.localMoment (sqrtScale (F.index n)) k n)‖ ≤
        C * ‖F.growingSaddleKernel n‖ * Real.exp (-(G.rate / 2) * sqrtScale (F.index n)) := by
  obtain ⟨C, hC, hb⟩ := F.fullMoment_absolute_leading_error G k
  have hA : 0 < ‖reflectionMomentFactor 0‖ := norm_pos_iff.mpr (reflectionMomentFactor_ne_zero 0)
  refine ⟨C / ‖reflectionMomentFactor 0‖, div_nonneg hC hA.le, ?_⟩
  filter_upwards [hb, F.eventually_scale_exp_le_saddleKernel (half_pos (G.rate_pos
    (doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos)))] with n hn hk
  have heq : reflectionMomentFactor k * F.saddleKernel n * F.data.localMoment (sqrtScale (F.index n)) k n =
      F.growingSaddleKernel n * ((-1 : ℂ) ^ k * F.data.localMoment (sqrtScale (F.index n)) k n) := by
    simp only [reflectionMomentFactor, growingSaddleKernel, pow_zero, mul_one]
    ring
  rw [heq] at hn
  calc
    _ ≤ C * (doubleScale m d A₁ A₂ z (F.index n) *
        Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate / 2) * sqrtScale (F.index n))) *
          Real.exp (-(G.rate / 2) * sqrtScale (F.index n)) := hn.trans_eq (by
      simp only [mul_assoc]
      rw [← Real.exp_add]
      congr 2
      ring_nf)
    _ ≤ C * ‖F.saddleKernel n‖ * Real.exp (-(G.rate / 2) * sqrtScale (F.index n)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC) (Real.exp_pos _).le
    _ = _ := by rw [growingSaddleKernel, norm_mul]; field_simp [hA.ne']

theorem gaussianNormalizer_bound :
    ∃ B ≥ 0, ∀ n : ℕ, ‖F.gaussianNormalizer n‖ ≤ B * sqrtScale (F.index n) ^ (1 / 2 : ℝ) := by
  obtain ⟨B, hB, hb⟩ := F.data.uniform_quadraticRoot_bounds
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨B / Real.Gamma (1 / 2 : ℝ), by positivity, fun n => ?_⟩
  have hp : 0 ≤ sqrtScale (F.index n) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  rw [gaussianNormalizer, norm_mul, Complex.norm_of_nonneg (div_nonneg hp hG.le)]
  calc
    _ ≤ B * (sqrtScale (F.index n) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (hb n).1 (div_nonneg hp hG.le)
    _ = _ := by ring


theorem eventually_growingSaddleKernel_ne_zero : ∀ᶠ n : ℕ in atTop, F.growingSaddleKernel n ≠ 0 :=
  F.eventually_saddleKernel_ne_zero.mono (fun _ hn => mul_ne_zero (reflectionMomentFactor_ne_zero 0) hn)

theorem normalizedFullMoment_tendsto (k : ℕ) :
    Tendsto (fun n => F.normalizedFullMoment G n k) atTop
      (𝓝 ((-(doubleSaddleScale d A₁ A₂ z : ℂ)) ^ k)) := by
  obtain ⟨C, hC, hrem⟩ := F.fullMoment_leading_error G k
  obtain ⟨B, hB, hN⟩ := F.gaussianNormalizer_bound
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖F.normalizedFullMoment G n k - (-1 : ℂ) ^ k *
        F.data.normalizedLocalMoment (sqrtScale (F.index n)) k n‖ ≤
        (B * C) * sqrtScale (F.index n) ^ (1 / 2 : ℝ) * Real.exp (-(G.rate / 2) * sqrtScale (F.index n)) := by
    filter_upwards [hrem, F.eventually_growingSaddleKernel_ne_zero] with n hn hk
    have hb := norm_normalized_remainder_le (A := F.gaussianNormalizer n) hk hn
    have he : F.normalizedFullMoment G n k - (-1 : ℂ) ^ k *
        F.data.normalizedLocalMoment (sqrtScale (F.index n)) k n =
        F.gaussianNormalizer n * (F.growingSaddleKernel n)⁻¹ * F.fullMoment G n k -
          F.gaussianNormalizer n * ((-1 : ℂ) ^ k * F.data.localMoment (sqrtScale (F.index n)) k n) := by
      dsimp only [normalizedFullMoment, QuadraticSaddleFamily.LocalSaddleData.normalizedLocalMoment,
        gaussianNormalizer]
      ring
    rw [he]
    calc
      _ ≤ ‖F.gaussianNormalizer n‖ * C * Real.exp (-(G.rate / 2) * sqrtScale (F.index n)) := hb
      _ ≤ (B * sqrtScale (F.index n) ^ (1 / 2 : ℝ)) * C *
          Real.exp (-(G.rate / 2) * sqrtScale (F.index n)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN n) hC) (Real.exp_pos _).le
      _ = _ := by ring
  have he : Tendsto (fun n => F.normalizedFullMoment G n k - (-1 : ℂ) ^ k *
      F.data.normalizedLocalMoment (sqrtScale (F.index n)) k n) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound (by
      simpa only [Function.comp_def, mul_zero, mul_assoc] using
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (G.rate / 2)
          (half_pos (G.rate_pos (doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos)))).comp
            (sqrtScale_tendsto.comp F.index_tendsto)).const_mul (B * C))
  have hl := (F.data.normalizedLocalMoment_tendsto (sqrtScale_tendsto.comp F.index_tendsto) k).const_mul ((-1 : ℂ) ^ k)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add, ReflectedSaddleFamily.toQuadratic,
    F.family.saddle_limit, ← mul_pow, neg_one_mul] using he.add hl

end ThisWork.Trajectory.ReflectedSaddleData

