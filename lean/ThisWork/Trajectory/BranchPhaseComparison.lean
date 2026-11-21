module
public import ThisWork.Trajectory.SqrtKernelNorm
public import ThisWork.Trajectory.SqrtKernelComparison
public import ThisWork.Trajectory.ReflectionApproximation
/-! Global compact phase comparison for all three branches. The twist cancels
exactly from the phase error, so the canonical comparison applies unchanged. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

noncomputable def sqrtBranchPhase (j : Branch) (c : ℝ) (s : ℂ) : ℂ :=
  sqrtPhase c s + twist j * s

theorem log_norm_kernel_twist {z : ℝ} (hz : 0 < z) (m d : ℕ) {A₁ A₂ : ℝ}
    (j : Branch) (n : ℕ) {x : ℂ} (hx : x ∈ kernelDomain A₁ A₂ n) :
    Real.log ‖kernel m d A₁ A₂ z j n x‖ =
      Real.log ‖kernel m d A₁ A₂ z .three n x‖ + (twist j * x).re := by
  rw [kernel_eq_twist, norm_mul, Complex.norm_exp,
    Real.log_mul (norm_ne_zero_iff.mpr (kernel_ne_zero hz m d .three n hx))
      (Real.exp_ne_zero _), Real.log_exp]

theorem log_norm_kernel_sub_branchPhase {z : ℝ} (hz : 0 < z) (m d : ℕ) {A₁ A₂ : ℝ}
    (j : Branch) (n : ℕ) {s : ℂ} (hs : (sqrtScale n : ℂ) * s ∈ kernelDomain A₁ A₂ n) :
    Real.log ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * s)‖ -
      sqrtScale n * (sqrtBranchPhase j (doubleSaddleScale d A₁ A₂ z) s).re =
      kernelPhaseError m d A₁ A₂ z n s := by
  rw [log_norm_kernel_twist hz m d j n hs]
  simp only [sqrtBranchPhase, kernelPhaseError, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- Uniform logarithmic asymptotics on every bounded part of an admissible
comparison region, retaining real `z > 0` as a parameter. -/
theorem uniform_log_norm_branch_region {d : ℕ} {A₁ A₂ z κ η M ε : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hκ : 0 < κ) (hη : 0 < η) (hε : 0 < ε)
    (hκc : κ ≤ doubleSaddleScale d A₁ A₂ z) (hcM : doubleSaddleScale d A₁ A₂ z ≤ M)
    (m : ℕ) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      |Real.log ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * s)‖ -
        Real.log (doubleScale m d A₁ A₂ z n) -
        sqrtScale n * (sqrtBranchPhase j (doubleSaddleScale d A₁ A₂ z) s).re| ≤ ε * sqrtScale n := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_canonical_kernel_disk hd h₁ h₂ hz m
  have hsmall : Tendsto (fun n => C * (1 + Real.log (sqrtScale n)) / sqrtScale n) atTop (𝓝 0) := by
    have hlog : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hi := tendsto_inv_atTop_zero.comp sqrtScale_tendsto
    simpa only [mul_zero, add_zero, div_eq_mul_inv, mul_add, add_mul, one_mul, mul_one, mul_assoc, Function.comp_def] using
      (hi.add (hlog.comp sqrtScale_tendsto)).const_mul C
  filter_upwards [uniform_kernelPhaseError_difference hd h₁ h₂ hz m hκ hη (hc.le.trans hcM) (half_pos hε),
    hb, eventually_bounded_slit_mapsTo_kernelDomain h₁ h₂ M,
    hsmall.eventually (gt_mem_nhds (half_pos hε))] with n hn hbase hdom herror s hs hregion
  have hslit : s ∈ Complex.slitPlane := by
    rcases hregion with hr | hi
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (hκ.trans_le hr))
    · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by intro he; rw [he, abs_zero] at hi; linarith))
  have hdiff := hn s hs hregion (c : ℂ) (by simpa only [Complex.norm_of_nonneg hc.le] using hcM) (Or.inl hκc)
  have hcD : (c : ℂ) ∈ saddleDisk c .three := by
    simpa only [saddleDisk, rho_three, mul_one] using mem_closedBall_self (show 0 ≤ c / 4 by positivity)
  have hbase' : |kernelPhaseError m d A₁ A₂ z n (c : ℂ) - Real.log (doubleScale m d A₁ A₂ z n)| ≤
      C * (1 + Real.log (sqrtScale n)) := by
    convert hbase (c : ℂ) hcD using 1
    congr 1
    dsimp only [kernelPhaseError, c]
    ring
  have herror' : C * (1 + Real.log (sqrtScale n)) ≤ ε / 2 * sqrtScale n :=
    ((div_lt_iff₀ (sqrtScale_pos hdom.1)).mp herror).le
  have he : Real.log ‖kernel m d A₁ A₂ z j n ((sqrtScale n : ℂ) * s)‖ -
      Real.log (doubleScale m d A₁ A₂ z n) - sqrtScale n * (sqrtBranchPhase j c s).re =
      (kernelPhaseError m d A₁ A₂ z n s - kernelPhaseError m d A₁ A₂ z n (c : ℂ)) +
      (kernelPhaseError m d A₁ A₂ z n (c : ℂ) - Real.log (doubleScale m d A₁ A₂ z n)) := by
    have h := log_norm_kernel_sub_branchPhase hz m d j n (hdom.2 s hs hslit)
    linarith
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hdiff (hbase'.trans herror')).trans_eq (by ring))

end ThisWork.Trajectory
