module
public import ThisWork.Trajectory.ReflectedLocalPhase
public import ThisWork.QuadraticSaddleWindow
/-! The nonzero Gaussian contribution of the actual reflected growing kernel. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric MeasureTheory Analytic
open scoped Topology OnePoint

structure ReflectedSaddleData (m d : ℕ) (A₁ A₂ z : ℝ) where
  d_pos : 0 < d
  A₁_pos : 0 < A₁
  A₂_pos : 0 < A₂
  z_pos : 0 < z
  family : ReflectedSaddleFamily d A₁ A₂ z
  data : (family.toQuadratic d_pos A₁_pos A₂_pos z_pos).LocalSaddleData

theorem exists_reflectedSaddleData {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) :
    Nonempty (ReflectedSaddleData m d A₁ A₂ z) := by
  obtain ⟨S⟩ := exists_compactReflectedSaddleFamily hd h₁ h₂ hz
  obtain ⟨D⟩ := (S.toQuadratic hd h₁ h₂ hz).exists_localSaddleData
  exact ⟨⟨hd, h₁, h₂, hz, S, D⟩⟩

namespace ReflectedSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
noncomputable def index (n : ℕ) : ℕ := n + F.data.shift + F.family.firstIndex
noncomputable def center (n : ℕ) : ℂ := F.family.saddle (n + F.data.shift)
noncomputable def saddleKernel (n : ℕ) : ℂ :=
  reflectedScaledKernel m d A₁ A₂ z (F.index n) (F.center n)
noncomputable def windowMoment (n k : ℕ) : ℂ :=
  ∫ t in -F.data.leftWidth..F.data.rightWidth,
    ((t : ℂ) + F.center n) ^ k * reflectedScaledKernel m d A₁ A₂ z (F.index n) ((t : ℂ) + F.center n)
noncomputable def gaussianNormalizer (n : ℕ) : ℂ :=
  F.data.quadraticRoot n * ((sqrtScale (F.index n) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)
noncomputable def normalizedWindowMoment (n k : ℕ) : ℂ :=
  F.gaussianNormalizer n * (F.saddleKernel n)⁻¹ * F.windowMoment n k

theorem index_tendsto : Tendsto F.index atTop atTop :=
  (tendsto_add_atTop_nat F.family.firstIndex).comp (tendsto_add_atTop_nat F.data.shift)

theorem eventually_saddleKernel_ne_zero : ∀ᶠ n : ℕ in atTop, F.saddleKernel n ≠ 0 := by
  have hc := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  filter_upwards [F.index_tendsto.eventually (eventually_reflectedScaledKernel_regular
    F.d_pos F.A₁_pos F.A₂_pos hc m)] with n hn
  have hs : F.center n ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) :=
    ball_subset_ball (by linarith : doubleSaddleScale d A₁ A₂ z / 16 ≤ doubleSaddleScale d A₁ A₂ z / 4)
      (F.family.saddle_mem (n + F.data.shift))
  exact (hn.2 _ hs).2.1

theorem eventually_windowMoment_eq_phase (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      F.windowMoment n k = F.saddleKernel n * F.data.localMoment (sqrtScale (F.index n)) k n := by
  filter_upwards [(tendsto_add_atTop_nat F.data.shift).eventually
    (F.family.eventually_kernel_eq_phase F.d_pos F.A₁_pos F.A₂_pos F.z_pos m)] with n hn
  rw [F.data.localMoment_eq_window, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have hp := F.data.widths_pos
  rw [uIcc_of_le (by linarith : -F.data.leftWidth ≤ F.data.rightWidth)] at ht
  have ht' : -F.data.leftWidth ≤ t ∧ t ≤ F.data.rightWidth := ht
  have hl : F.data.leftWidth < doubleSaddleScale d A₁ A₂ z / 16 := F.data.widths_lt.1
  have hr : F.data.rightWidth < doubleSaddleScale d A₁ A₂ z / 16 := F.data.widths_lt.2
  have hb : (t : ℂ) ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16) := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  dsimp only [windowMoment, saddleKernel, index, center]
  rw [hn _ hb]
  simp only [ReflectedSaddleFamily.toQuadratic, parameterShift_nat, mul_one, one_mul]
  ring

theorem normalizedWindowMoment_tendsto (k : ℕ) :
    Tendsto (fun n => F.normalizedWindowMoment n k) atTop
      (𝓝 ((doubleSaddleScale d A₁ A₂ z : ℂ) ^ k)) := by
  have hl := F.data.normalizedLocalMoment_tendsto (sqrtScale_tendsto.comp F.index_tendsto) k
  apply (show Tendsto (fun n => F.data.normalizedLocalMoment (sqrtScale (F.index n)) k n) atTop
    (𝓝 ((doubleSaddleScale d A₁ A₂ z : ℂ) ^ k)) from by
      simpa only [Function.comp_apply, ReflectedSaddleFamily.toQuadratic, F.family.saddle_limit] using hl).congr'
  filter_upwards [F.eventually_windowMoment_eq_phase k, F.eventually_saddleKernel_ne_zero] with n hn hK
  symm
  rw [normalizedWindowMoment, hn]
  rw [mul_assoc, ← mul_assoc ((F.saddleKernel n)⁻¹), inv_mul_cancel₀ hK, one_mul]
  rfl

end ReflectedSaddleData
end ThisWork.Trajectory
