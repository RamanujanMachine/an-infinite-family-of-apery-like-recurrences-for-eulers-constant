module
public import ThisWork.Trajectory.SqrtCenteredPhase
public import ThisWork.QuadraticSaddleWindow
public import ThisWork.WindowOrientation
/-! Identification of the canonical saddle window with its Gaussian model. -/
@[expose] public section
namespace ThisWork.Trajectory.SqrtSaddleFamily
open Set Filter Metric MeasureTheory Analytic
open scoped Topology OnePoint

theorem eventually_contourWindow_eq_phase {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (S : SqrtSaddleFamily d A₁ A₂ z) (D : (S.toQuadratic hd h₁ h₂ hz).LocalSaddleData)
    (q k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      contourWindow .three (S.saddle (n + D.shift)) D.leftWidth D.rightWidth
        (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three (S.saddle (n + D.shift)))
        (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three (S.saddle (n + D.shift)))
        (fun s => s ^ k * kernel q d A₁ A₂ z .three (n + D.shift + S.firstIndex)
          ((sqrtScale (n + D.shift + S.firstIndex) : ℂ) * s)) =
      kernel q d A₁ A₂ z .three (n + D.shift + S.firstIndex)
        ((sqrtScale (n + D.shift + S.firstIndex) : ℂ) * S.saddle (n + D.shift)) *
        D.localMoment (sqrtScale (n + D.shift + S.firstIndex)) k n := by
  filter_upwards [(tendsto_add_atTop_nat D.shift).eventually
    (S.eventually_kernel_eq_phase hd h₁ h₂ hz q)] with n hn
  rw [contourWindow_eq_ray_window (doubleSaddleScale_pos hd h₁ h₂ hz) .three
    (S.saddle_mem_disk hd h₁ h₂ hz (n + D.shift)), D.localMoment_eq_window]
  simp only [branchOrientation, saddleTangent, one_mul,
    show (S.toQuadratic hd h₁ h₂ hz).tangent = Complex.I from rfl,
    show (S.toQuadratic hd h₁ h₂ hz).saddle = S.saddle from rfl]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by linarith [D.widths_pos.1, D.widths_pos.2] :
    -D.leftWidth ≤ D.rightWidth)] at ht
  have hta : -D.leftWidth ≤ t ∧ t ≤ D.rightWidth := ht
  have hl : D.leftWidth < doubleSaddleScale d A₁ A₂ z / 16 := D.widths_lt.1
  have hr : D.rightWidth < doubleSaddleScale d A₁ A₂ z / 16 := D.widths_lt.2
  have hball : (t : ℂ) * Complex.I ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16) := by
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_lt]
    exact ⟨by linarith, by linarith⟩
  dsimp only
  rw [hn _ hball]
  simp only [parameterShift_nat]
  ring

end ThisWork.Trajectory.SqrtSaddleFamily
