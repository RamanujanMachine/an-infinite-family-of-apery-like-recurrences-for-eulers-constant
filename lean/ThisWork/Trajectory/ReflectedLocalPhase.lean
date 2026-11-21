module
public import ThisWork.Trajectory.ReflectedKernelPhase
/-! Centered compact Gaussian phases for the actual square-root saddle. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology OnePoint

namespace ReflectedSaddleFamily

noncomputable def toQuadratic {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (S : ReflectedSaddleFamily d A₁ A₂ z) : QuadraticSaddleFamily where
  saddle := S.saddle
  radius := doubleSaddleScale d A₁ A₂ z / 16
  radius_pos := div_pos (doubleSaddleScale_pos hd h₁ h₂ hz) (by norm_num)
  equation := S.shiftedEquation
  continuous_equation := S.continuous_shiftedEquation
  holomorphic_equation := S.differentiableOn_shiftedEquation
  equation_zero := S.shiftedEquation_zero
  equation_simple := S.shiftedEquation_simple
  tangent := 1
  norm_tangent := norm_one
  positive_limit := by
    have hc := doubleSaddleScale_pos hd h₁ h₂ hz
    have he : (fun t => S.shiftedEquation t ∞) =
        (fun t => -sqrtEquation (doubleSaddleScale d A₁ A₂ z)
          (t + (doubleSaddleScale d A₁ A₂ z : ℂ))) := funext S.shiftedEquation_limit
    rw [he, deriv.fun_neg, deriv_comp_add_const, zero_add,
      (hasDerivAt_sqrtEquation hc (by simp [hc.ne', Complex.one_mem_slitPlane])).deriv]
    have h : -(-(2 / (doubleSaddleScale d A₁ A₂ z : ℂ))) / 2 * (1 : ℂ) ^ 2 =
        ((1 / doubleSaddleScale d A₁ A₂ z : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h, Complex.ofReal_re]
    positivity

theorem eventually_kernel_eq_phase {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (S : ReflectedSaddleFamily d A₁ A₂ z) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16),
      reflectedScaledKernel m d A₁ A₂ z (n + S.firstIndex) (t + S.saddle n) =
      reflectedScaledKernel m d A₁ A₂ z (n + S.firstIndex) (S.saddle n) *
      Complex.exp (-(sqrtScale (n + S.firstIndex) : ℂ) * (S.toQuadratic hd h₁ h₂ hz).phase t n) := by
  have hc := doubleSaddleScale_pos hd h₁ h₂ hz
  filter_upwards [(tendsto_add_atTop_nat S.firstIndex).eventually
    (eventually_reflectedScaledKernel_regular hd h₁ h₂ hc m)] with n hn
  have ha : S.saddle n ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) :=
    ball_subset_ball (by linarith : doubleSaddleScale d A₁ A₂ z / 16 ≤ doubleSaddleScale d A₁ A₂ z / 4)
      (S.saddle_mem n)
  obtain ⟨p, hp0, hp, hk⟩ := exists_normalized_phase_ball ha
    (Complex.ofReal_ne_zero.mpr (sqrtScale_pos hn.1).ne')
    (fun s hs => (hn.2 s hs).1.differentiableWithinAt)
    (fun s hs => (hn.2 s hs).2.1) (fun s hs => (hn.2 s hs).2.2)
  have hmap : ∀ t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16),
      t + S.saddle n ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) :=
    fun _ ht => ball_subset_ball (by linarith : doubleSaddleScale d A₁ A₂ z / 8 ≤ doubleSaddleScale d A₁ A₂ z / 4)
      (S.shifted_mem ht n)
  have hcomp : ∀ t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16),
      HasDerivAt (fun u => p (u + S.saddle n)) (-S.shiftedEquation t n) t := by
    intro t ht
    simpa only [shiftedEquation, reflectedParameterEquation, sequenceFamily_nat, Function.comp_def, id_eq, mul_one] using
      (hp _ (hmap t ht)).comp t ((hasDerivAt_id t).add_const (S.saddle n))
  have he := eq_neg_segmentIntegral_of_derivative (div_pos hc (by norm_num))
    (S.differentiableOn_shiftedEquation n) (by simpa only [zero_add] using hp0) hcomp
  intro t ht
  simpa only [QuadraticSaddleFamily.phase, toQuadratic, he ht] using hk _ (hmap t ht)

end ReflectedSaddleFamily
end ThisWork.Trajectory
