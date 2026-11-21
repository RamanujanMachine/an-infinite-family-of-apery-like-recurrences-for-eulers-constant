module
public import ThisWork.Trajectory.SqrtCompactFamily
/-! Centered compact Gaussian phases for the actual square-root saddle. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology OnePoint

namespace SqrtSaddleFamily

noncomputable def toQuadratic {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (S : SqrtSaddleFamily d A₁ A₂ z) : QuadraticSaddleFamily where
  saddle := S.saddle
  radius := doubleSaddleScale d A₁ A₂ z / 16
  radius_pos := div_pos (doubleSaddleScale_pos hd h₁ h₂ hz) (by norm_num)
  equation := S.shiftedEquation
  continuous_equation := S.continuous_shiftedEquation
  holomorphic_equation := S.differentiableOn_shiftedEquation
  equation_zero := S.shiftedEquation_zero
  equation_simple := S.shiftedEquation_simple
  tangent := Complex.I
  norm_tangent := Complex.norm_I
  positive_limit := by
    have hc := doubleSaddleScale_pos hd h₁ h₂ hz
    have he : (fun t => S.shiftedEquation t ∞) =
        (fun t => sqrtEquation (doubleSaddleScale d A₁ A₂ z)
          (t + (doubleSaddleScale d A₁ A₂ z : ℂ))) := funext S.shiftedEquation_limit
    rw [he, deriv_comp_add_const, zero_add,
      (hasDerivAt_sqrtEquation hc (by simp [hc.ne', Complex.one_mem_slitPlane])).deriv]
    have h : -(2 / (doubleSaddleScale d A₁ A₂ z : ℂ)) / 2 * Complex.I ^ 2 =
        ((1 / doubleSaddleScale d A₁ A₂ z : ℝ) : ℂ) := by
      rw [Complex.I_sq]
      push_cast
      ring
    rw [h, Complex.ofReal_re]
    positivity

theorem eventually_kernel_eq_phase {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (S : SqrtSaddleFamily d A₁ A₂ z) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16),
      kernel q d A₁ A₂ z .three (n + S.firstIndex)
        ((sqrtScale (n + S.firstIndex) : ℂ) * (t + S.saddle n)) =
      kernel q d A₁ A₂ z .three (n + S.firstIndex)
        ((sqrtScale (n + S.firstIndex) : ℂ) * S.saddle n) *
      Complex.exp (-(sqrtScale (n + S.firstIndex) : ℂ) * (S.toQuadratic hd h₁ h₂ hz).phase t n) := by
  have hc := doubleSaddleScale_pos hd h₁ h₂ hz
  filter_upwards [(tendsto_add_atTop_nat S.firstIndex).eventually
    (eventually_sqrtDisk_mapsTo_kernelDomain h₁ h₂ hc)] with n hn
  have ha : S.saddle n ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) :=
    ball_subset_ball (by linarith : doubleSaddleScale d A₁ A₂ z / 16 ≤ doubleSaddleScale d A₁ A₂ z / 4)
      (S.saddle_mem n)
  obtain ⟨p, hp0, hp, hk⟩ := exists_scaled_kernel_phase hz q d .three hn.1 ha
    (fun _ hs => hn.2 (by simpa only [saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs))
  have hmap : ∀ t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16),
      t + S.saddle n ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) :=
    fun _ ht => ball_subset_ball (by linarith : doubleSaddleScale d A₁ A₂ z / 8 ≤ doubleSaddleScale d A₁ A₂ z / 4)
      (S.shifted_mem ht n)
  have hcomp : ∀ t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16),
      HasDerivAt (fun u => p (u + S.saddle n)) (-S.shiftedEquation t n) t := by
    intro t ht
    simpa only [shiftedEquation, sqrtParameterEquation, sequenceFamily_nat, Function.comp_def, id_eq, mul_one] using
      (hp _ (hmap t ht)).comp t ((hasDerivAt_id t).add_const (S.saddle n))
  have he := eq_neg_segmentIntegral_of_derivative (div_pos hc (by norm_num))
    (S.differentiableOn_shiftedEquation n) (by simpa only [zero_add] using hp0) hcomp
  intro t ht
  simpa only [QuadraticSaddleFamily.phase, toQuadratic, he ht] using hk _ (hmap t ht)

end SqrtSaddleFamily
end ThisWork.Trajectory
