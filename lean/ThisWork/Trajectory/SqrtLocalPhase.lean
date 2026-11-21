module

public import ThisWork.Trajectory.SqrtSaddles
public import ThisWork.LocalKernelPhase

/-! Genuine local Laplace phases for the square-root-scaled trajectory kernel. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

theorem logDeriv_scaled_kernel {z : ℝ} (hz : 0 < z) (m d : ℕ)
    {A₁ A₂ : ℝ} (j : Branch) (n : ℕ) {s : ℂ}
    (hs : (sqrtScale n : ℂ) * s ∈ Analytic.kernelDomain A₁ A₂ n) :
    logDeriv (fun t => kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * t)) s =
      (sqrtScale n : ℂ) * exactSqrtEquation d A₁ A₂ z j n s := by
  have hscale : HasDerivAt (fun t : ℂ => (sqrtScale n : ℂ) * t) (sqrtScale n : ℂ) s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (sqrtScale n : ℂ)
  rw [logDeriv_fun_comp ((differentiableOn_kernel hz m d A₁ A₂ j n).differentiableAt
    ((Analytic.isOpen_kernelDomain A₁ A₂ n).mem_nhds hs)) hscale.differentiableAt,
    logDeriv_kernel hz m d j n hs, hscale.deriv, mul_comm]
  rfl

theorem exists_scaled_kernel_phase {z : ℝ} (hz : 0 < z) (m d : ℕ)
    {A₁ A₂ : ℝ} (j : Branch) {n : ℕ} (hn : 0 < n)
    {a b : ℂ} {r : ℝ} (ha : a ∈ ball b r)
    (hmap : MapsTo (fun s : ℂ => (sqrtScale n : ℂ) * s)
      (ball b r) (Analytic.kernelDomain A₁ A₂ n)) :
    ∃ p : ℂ → ℂ, p a = 0 ∧
      (∀ s ∈ ball b r, HasDerivAt p (-exactSqrtEquation d A₁ A₂ z j n s) s) ∧
      ∀ s ∈ ball b r,
        kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * s) =
          kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * a) *
            Complex.exp (-(sqrtScale n : ℂ) * p s) := by
  apply Analytic.exists_normalized_phase_ball ha (Complex.ofReal_ne_zero.mpr (sqrtScale_pos hn).ne')
  · exact (differentiableOn_kernel hz m d A₁ A₂ j n).comp
      (differentiableOn_id.const_mul (sqrtScale n : ℂ)) hmap
  · exact fun s hs => kernel_ne_zero hz m d j n (hmap hs)
  · exact fun s hs => logDeriv_scaled_kernel hz m d j n (hmap hs)

/-- The actual canonical kernel has a genuine quadratic Laplace phase at its moving saddle. -/
theorem eventually_exists_exact_sqrt_phase {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∃ a ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4),
        ‖a - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ C / sqrtScale n ∧
        ∃ p : ℂ → ℂ, p a = 0 ∧ deriv p a = 0 ∧ deriv (deriv p) a ≠ 0 ∧
          (∀ s ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4),
            HasDerivAt p (-exactSqrtEquation d A₁ A₂ z .three n s) s) ∧
          ∀ s ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4),
            kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s) =
              kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * a) *
                Complex.exp (-(sqrtScale n : ℂ) * p s) := by
  obtain ⟨r, _, hrD, C, hC, hb⟩ := exists_exact_sqrt_saddle hd h₁ h₂ hz
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_sqrtDisk_mapsTo_kernelDomain h₁ h₂
    (doubleSaddleScale_pos hd h₁ h₂ hz)] with n hn hdom
  obtain ⟨a, ha, hzero, hsimple, hdist, _⟩ := hn
  obtain ⟨p, hpa, hp, he⟩ := exists_scaled_kernel_phase hz m d .three hdom.1 (hrD ha)
    (fun s hs => hdom.2 (by
      simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs))
  have hquad := Analytic.phase_simple_saddle (hrD ha) hp hzero hsimple
  exact ⟨a, hrD ha, hdist, p, hpa, hquad.1, hquad.2, hp, he⟩

end ThisWork.Trajectory
