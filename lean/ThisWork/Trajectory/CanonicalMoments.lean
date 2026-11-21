module
public import ThisWork.Trajectory.SqrtWindow
public import ThisWork.Trajectory.CanonicalRemainder
public import ThisWork.FullMomentAsymptotics
/-! Normalized complete canonical moments at square-root scale. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology OnePoint

structure CanonicalSaddleData (m d : ℕ) (A₁ A₂ z : ℝ) where
  d_pos : 0 < d
  A₁_pos : 0 < A₁
  A₂_pos : 0 < A₂
  z_pos : 0 < z
  family : SqrtSaddleFamily d A₁ A₂ z
  data : (family.toQuadratic d_pos A₁_pos A₂_pos z_pos).LocalSaddleData

theorem exists_canonicalSaddleData {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) :
    Nonempty (CanonicalSaddleData m d A₁ A₂ z) := by
  obtain ⟨S⟩ := exists_compactSaddleFamily hd h₁ h₂ hz
  obtain ⟨D⟩ := (S.toQuadratic hd h₁ h₂ hz).exists_localSaddleData
  exact ⟨⟨hd, h₁, h₂, hz, S, D⟩⟩

namespace CanonicalSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : CanonicalSaddleData m d A₁ A₂ z)
noncomputable def index (n : ℕ) : ℕ := n + F.data.shift + F.family.firstIndex
noncomputable def center (n : ℕ) : ℂ := F.family.saddle (n + F.data.shift)
noncomputable def saddleKernel (n : ℕ) : ℂ :=
  kernel m d A₁ A₂ z .three (F.index n) ((sqrtScale (F.index n) : ℂ) * F.center n)
noncomputable def fullMoment (n k : ℕ) : ℂ :=
  hankelIntegral (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three (F.center n))
    (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three (F.center n))
    (fun s => s ^ k * kernel m d A₁ A₂ z .three (F.index n) ((sqrtScale (F.index n) : ℂ) * s))
noncomputable def gaussianNormalizer (n : ℕ) : ℂ :=
  F.data.quadraticRoot n * ((sqrtScale (F.index n) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)
noncomputable def normalizedFullMoment (n k : ℕ) : ℂ :=
  F.gaussianNormalizer n * (F.saddleKernel n)⁻¹ * F.fullMoment n k

theorem index_tendsto : Tendsto F.index atTop atTop :=
  (tendsto_add_atTop_nat F.family.firstIndex).comp (tendsto_add_atTop_nat F.data.shift)

theorem center_mem (n : ℕ) : F.center n ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three :=
  F.family.saddle_mem_disk F.d_pos F.A₁_pos F.A₂_pos F.z_pos _

theorem eventually_saddleKernel_ne_zero : ∀ᶠ n : ℕ in atTop, F.saddleKernel n ≠ 0 := by
  filter_upwards [F.index_tendsto.eventually (eventually_sqrtDisk_mapsTo_kernelDomain
    F.A₁_pos F.A₂_pos (doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos))] with n hn
  exact kernel_ne_zero F.z_pos m d .three (F.index n) (hn.2 (F.center_mem n))

theorem fullMoment_leading_error (k : ℕ) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖F.fullMoment n k - F.saddleKernel n * F.data.localMoment (sqrtScale (F.index n)) k n‖ ≤
        C * ‖F.saddleKernel n‖ * Real.exp (-ε * sqrtScale (F.index n)) := by
  obtain ⟨ε, hε, C, hC, hb⟩ := uniform_full_canonical_window_remainder
    F.d_pos F.A₁_pos F.A₂_pos F.z_pos F.data.widths_pos.1 F.data.widths_pos.2
      F.data.widths_lt.1 F.data.widths_lt.2 m k F.family.errorConstant
  refine ⟨ε, hε, C, hC, ?_⟩
  filter_upwards [F.index_tendsto.eventually hb,
    F.family.eventually_contourWindow_eq_phase F.d_pos F.A₁_pos F.A₂_pos F.z_pos F.data m k]
    with n hn hw
  have he := hn (F.center n) (F.center_mem n) (F.family.displacement (n + F.data.shift))
  dsimp only [center, index] at he
  rw [hw] at he
  exact he

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

theorem normalizedFullMoment_tendsto (k : ℕ) :
    Tendsto (fun n => F.normalizedFullMoment n k) atTop
      (𝓝 ((doubleSaddleScale d A₁ A₂ z : ℂ) ^ k)) := by
  obtain ⟨ε, hε, C, hC, hrem⟩ := F.fullMoment_leading_error k
  obtain ⟨B, hB, hN⟩ := F.gaussianNormalizer_bound
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖F.normalizedFullMoment n k - F.data.normalizedLocalMoment (sqrtScale (F.index n)) k n‖ ≤
        (B * C) * sqrtScale (F.index n) ^ (1 / 2 : ℝ) * Real.exp (-ε * sqrtScale (F.index n)) := by
    filter_upwards [hrem, F.eventually_saddleKernel_ne_zero] with n hn hk
    have hb := norm_normalized_remainder_le (A := F.gaussianNormalizer n) hk hn
    calc
      _ ≤ ‖F.gaussianNormalizer n‖ * C * Real.exp (-ε * sqrtScale (F.index n)) := hb
      _ ≤ (B * sqrtScale (F.index n) ^ (1 / 2 : ℝ)) * C *
          Real.exp (-ε * sqrtScale (F.index n)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hN n) hC) (Real.exp_pos _).le
      _ = _ := by ring
  have he : Tendsto (fun n => F.normalizedFullMoment n k -
      F.data.normalizedLocalMoment (sqrtScale (F.index n)) k n) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound (by
      simpa only [Function.comp_def, mul_zero, mul_assoc] using
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) ε hε).comp
          (sqrtScale_tendsto.comp F.index_tendsto)).const_mul (B * C))
  have hl := F.data.normalizedLocalMoment_tendsto (sqrtScale_tendsto.comp F.index_tendsto) k
  simpa only [Function.comp_apply, sub_add_cancel, zero_add, SqrtSaddleFamily.toQuadratic,
    F.family.saddle_limit] using he.add hl

end CanonicalSaddleData
end ThisWork.Trajectory
