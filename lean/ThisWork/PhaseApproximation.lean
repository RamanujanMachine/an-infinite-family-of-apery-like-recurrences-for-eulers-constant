module

public import ThisWork.LocalKernelPhase

/-! Uniform comparison of the exact local Gamma phases with the limiting phase. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem uniform_local_phase_approximation {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ (p : ℂ → ℂ) (a : ℂ),
      a ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4) →
      p a = 0 →
      (∀ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
        HasDerivAt p (-exactSaddleEquation α₁ α₂ j n s) s) →
      ∀ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
        ‖p s - (limitingPhase j (saddleScale α₁ α₂) a - limitingPhase j (saddleScale α₁ α₂) s)‖ ≤
          ‖s - a‖ * (C * smallParameter n) := by
  obtain ⟨C, hC, hb⟩ := uniform_exactSaddleEquation_disk h₁ h₂ j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_differentiableOn_exactSaddleEquation h₁ h₂ j] with n hn hhol
  intro p a ha hpa hp s hs
  have hφ : ∀ t ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
      HasDerivAt (fun u => -limitingPhase j (saddleScale α₁ α₂) u)
        (-limitingEquation j (saddleScale α₁ α₂) t) t :=
    fun t ht => (hasDerivAt_limitingPhase j (saddleScale_pos h₁ h₂)
      ((div_pos_real_mem_slitPlane_iff (saddleScale_pos h₁ h₂) t).mpr
        (saddleDisk_mem_slitPlane (saddleScale_pos h₁ h₂) j (ball_subset_closedBall ht)))).neg
  have he := norm_primitive_sub_le_ball ha hs hp hφ
    (hhol.continuousOn.neg.fun_sub
      (differentiableOn_limitingEquation_disk (saddleScale_pos h₁ h₂) j).continuousOn.neg)
    (fun t ht => by
      simpa only [neg_sub_neg, norm_sub_rev] using hn t (ball_subset_closedBall ht))
  simpa only [hpa, sub_zero, neg_sub_neg] using he

/-- Exact local phases at the moving Gamma saddles, with a uniform quantitative
comparison to the limiting phase. Every object here belongs to the actual
kernel, rather than to a separately assumed asymptotic model. -/
theorem eventually_exists_exact_local_phase {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) :
    ∃ C ≥ 0, ∃ D ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∃ a ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
        exactSaddleEquation α₁ α₂ j n a = 0 ∧
        deriv (exactSaddleEquation α₁ α₂ j n) a ≠ 0 ∧
        ‖a - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ C * smallParameter n ∧
        ∃ p : ℂ → ℂ, p a = 0 ∧ deriv p a = 0 ∧ deriv (deriv p) a ≠ 0 ∧
          (∀ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
            HasDerivAt p (-exactSaddleEquation α₁ α₂ j n s) s) ∧
          (∀ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
            kernel α₁ α₂ j n ((largeScale n : ℂ) * s) =
              kernel α₁ α₂ j n ((largeScale n : ℂ) * a) *
                Complex.exp (-(largeScale n : ℂ) * p s)) ∧
          ∀ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4),
            ‖p s - (limitingPhase j (saddleScale α₁ α₂) a - limitingPhase j (saddleScale α₁ α₂) s)‖ ≤
              ‖s - a‖ * (D * smallParameter n) := by
  obtain ⟨r, _, _, C, hC, hzeros⟩ := exists_exact_saddle h₁ h₂ j
  obtain ⟨D, hD, happrox⟩ := uniform_local_phase_approximation h₁ h₂ j
  have hsmall : ∀ᶠ n : ℕ in atTop, C * smallParameter n < saddleScale α₁ α₂ / 4 :=
    (show Tendsto (fun n => C * smallParameter n) atTop (𝓝 0) from
      by simpa only [mul_zero] using smallParameter_tendsto.const_mul C).eventually
      (gt_mem_nhds (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))
  refine ⟨C, hC, D, hD, ?_⟩
  filter_upwards [hzeros, hsmall, happrox, eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j]
    with n hn hsmall happrox hdom
  obtain ⟨a, _, hz, hd, hdist, _⟩ := hn
  have ha : a ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4) := by
    simpa only [mem_ball, dist_eq_norm] using hdist.trans_lt hsmall
  obtain ⟨p, hpa, hp, hkernel⟩ := exists_scaled_kernel_phase j hdom.1 ha
    (fun s hs => hdom.2 (ball_subset_closedBall hs))
  have hsimple := phase_simple_saddle ha hp hz hd
  exact ⟨a, ha, hz, hd, hdist, p, hpa, hsimple.1, hsimple.2, hp, hkernel,
    happrox p a ha hpa hp⟩

end ThisWork
