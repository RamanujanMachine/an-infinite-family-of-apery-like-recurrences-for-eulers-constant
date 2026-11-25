module

public import ThisWork.ExactSaddles
public import ThisWork.LocalPhaseTools

/-! Exact normalized holomorphic phases for the actual arbitrary-rank
Gamma kernels. No principal logarithm of Gamma is introduced. -/

@[expose] public section
namespace ThisWork

open Set Metric Filter

theorem logDeriv_scaled_kernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) {s : ℂ}
    (hs : (largeScale r n : ℂ) * s ∈ kernelDomain r A n) :
    logDeriv (fun t => kernel r b A z j n ((largeScale r n : ℂ) * t)) s =
      (largeScale r n : ℂ) * exactSaddleEquation r A z j n s := by
  have hscale : HasDerivAt (fun t : ℂ => (largeScale r n : ℂ) * t) (largeScale r n : ℂ) s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (largeScale r n : ℂ)
  rw [logDeriv_fun_comp (differentiableAt_kernel b z j n hs) hscale.differentiableAt,
    ← exactSaddleEquation_eq_logDeriv b z j n hs, hscale.deriv, mul_comm]

/-- A genuine local Laplace phase for the arbitrary-rank Gamma product. -/
theorem exists_scaled_kernel_phase {r : ℕ} {A : Fin (r - 1) → ℝ}
    (b : ℕ) (z : ℝ) (j : ℤ) {n : ℕ} (hn : 0 < n)
    {a auxB : ℂ} {δ : ℝ} (ha : a ∈ ball auxB δ)
    (hmap : MapsTo (fun s : ℂ => (largeScale r n : ℂ) * s)
      (ball auxB δ) (kernelDomain r A n)) :
    ∃ p : ℂ → ℂ, p a = 0 ∧
      (∀ s ∈ ball auxB δ, HasDerivAt p (-exactSaddleEquation r A z j n s) s) ∧
      ∀ s ∈ ball auxB δ,
        kernel r b A z j n ((largeScale r n : ℂ) * s) =
          kernel r b A z j n ((largeScale r n : ℂ) * a) *
            Complex.exp (-(largeScale r n : ℂ) * p s) := by
  apply Analytic.exists_normalized_phase_ball ha
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne')
  · intro s hs
    exact ((differentiableAt_kernel b z j n (hmap hs)).comp s
      (by fun_prop)).differentiableWithinAt
  · exact fun s hs => kernel_ne_zero b z j n (hmap hs)
  · exact fun s hs => logDeriv_scaled_kernel b z j n (hmap hs)

/-- Every fixed disk contained in the slit plane is eventually a holomorphic
domain of the scaled kernel. The upper Gamma poles escape to the right. -/
theorem eventually_differentiableOn_scaled_kernel_ball {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ)
    {auxB : ℂ} {δ : ℝ} (hslit : ball auxB δ ⊆ Complex.slitPlane) :
    ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (fun s => kernel r b A z j n ((largeScale r n : ℂ) * s)) (ball auxB δ) := by
  filter_upwards [eventually_scaled_slit_in_kernelDomain hr hA (‖auxB‖ + δ)] with n hn s hs
  have hnorm : ‖s - auxB‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hs
  have hre : s.re ≤ ‖auxB‖ + δ := by
    linarith [Complex.re_le_norm s, norm_sub_norm_le s auxB]
  exact ((differentiableAt_kernel b z j n (hn s hre (hslit hs))).comp s
    (by fun_prop)).differentiableWithinAt

end ThisWork
