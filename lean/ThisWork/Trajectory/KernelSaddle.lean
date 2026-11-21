module

public import ThisWork.Trajectory.KernelIdentities
public import ThisWork.Trajectory.SqrtSaddleEquation
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The double-minimum saddle equation is the actual kernel's logarithmic derivative. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter
open scoped Topology

theorem add_nat_mul_mem_slitPlane (d n : ℕ) {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    (d : ℂ) * n + x ∈ Complex.slitPlane := by
  rcases Complex.mem_slitPlane_iff.mp hx with h | h
  · apply Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      mul_zero, sub_zero]
    positivity
  · apply Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simpa using h

theorem logDeriv_kernel {z : ℝ} (hz : 0 < z) (m d : ℕ)
    {A₁ A₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ Analytic.kernelDomain A₁ A₂ n) :
    logDeriv (kernel m d A₁ A₂ z j n) x = kernelLogDerivative d A₁ A₂ z j n x := by
  let : PositiveArgument := ⟨z, hz⟩
  have hp := Analytic.not_neg_nat_of_mem_slitPlane hx.1
  have hpd := Analytic.not_neg_nat_of_mem_slitPlane (add_nat_mul_mem_slitPlane d n hx.1)
  have hd₀ := Complex.differentiableAt_Gamma x hp
  have hdarg : HasDerivAt (fun y : ℂ => (d : ℂ) * n + y) 1 x :=
    (hasDerivAt_id x).const_add _
  have hdD := (Complex.differentiableAt_Gamma _ hpd).comp x hdarg.differentiableAt
  have hdK := (Analytic.differentiableOn_kernel A₁ A₂ j n).differentiableAt
    ((Analytic.isOpen_kernelDomain A₁ A₂ n).mem_nhds hx)
  have he : kernel m d A₁ A₂ z j n =ᶠ[𝓝 x]
      (fun y => Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)) *
        (Complex.Gamma ((d : ℂ) * n + y) / Complex.Gamma y *
          Analytic.normalizedKernel A₁ A₂ j n y)) :=
    Filter.mem_of_superset (Complex.isOpen_slitPlane.mem_nhds hx.1) fun y hy =>
      kernel_eq_gamma_quotient hz m d A₁ A₂ j n (Analytic.not_neg_nat_of_mem_slitPlane hy)
  rw [Filter.EventuallyEq.eq_of_nhds (logDeriv_congr_nhds he)]
  rw [logDeriv_const_mul _ _ (Complex.exp_ne_zero _),
    logDeriv_fun_mul (f := fun y : ℂ => Complex.Gamma ((d : ℂ) * n + y) / Complex.Gamma y)
      (g := Analytic.normalizedKernel A₁ A₂ j n) x (div_ne_zero (Complex.Gamma_ne_zero hpd) (Complex.Gamma_ne_zero hp))
      (Analytic.kernel_ne_zero j n hx) (hdD.fun_div hd₀ (Complex.Gamma_ne_zero hp)) hdK,
    logDeriv_fun_div (f := fun y : ℂ => Complex.Gamma ((d : ℂ) * n + y))
      (g := Complex.Gamma) x (Complex.Gamma_ne_zero hpd) (Complex.Gamma_ne_zero hp) hdD hd₀,
    Analytic.logDeriv_kernel j n hx]
  rw [hdarg.logDeriv_Gamma hpd, ← Complex.digamma_def]
  simp only [kernelLogDerivative, Analytic.kernelLogDerivative, Analytic.kernelTwist]
  change _ - _ + (3 * _ - _ - _ + (twist j - (Real.log z : ℂ))) = _
  ring

theorem kernel_ne_zero {z : ℝ} (hz : 0 < z) (m d : ℕ)
    {A₁ A₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ Analytic.kernelDomain A₁ A₂ n) : kernel m d A₁ A₂ z j n x ≠ 0 := by
  rw [kernel_eq_gamma_quotient hz m d A₁ A₂ j n (Analytic.not_neg_nat_of_mem_slitPlane hx.1)]
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero
    (div_ne_zero
      (Complex.Gamma_ne_zero (Analytic.not_neg_nat_of_mem_slitPlane (add_nat_mul_mem_slitPlane d n hx.1)))
      (Complex.Gamma_ne_zero (Analytic.not_neg_nat_of_mem_slitPlane hx.1)))
    (@Analytic.kernel_ne_zero ⟨z, hz⟩ A₁ A₂ j n x hx))

theorem differentiableOn_kernel {z : ℝ} (hz : 0 < z)
    (m d : ℕ) (A₁ A₂ : ℝ) (j : Branch) (n : ℕ) :
    DifferentiableOn ℂ (kernel m d A₁ A₂ z j n) (Analytic.kernelDomain A₁ A₂ n) := by
  let : PositiveArgument := ⟨z, hz⟩
  have h := (((ascPochhammer ℂ (d * n)).differentiableOn).mul
    (Analytic.differentiableOn_kernel A₁ A₂ j n)).const_mul
      (Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)))
  apply h.congr
  intro x hx
  simpa only [Pi.mul_apply, mul_assoc] using kernel_eq_normalized_polynomial hz m d A₁ A₂ j n
    (Analytic.not_neg_nat_of_mem_slitPlane hx.1)

theorem differentiableOn_kernelLogDerivative {z : ℝ} (hz : 0 < z)
    (d : ℕ) (A₁ A₂ : ℝ) (j : Branch) (n : ℕ) :
    DifferentiableOn ℂ (kernelLogDerivative d A₁ A₂ z j n)
      (Analytic.kernelDomain A₁ A₂ n) := by
  have hk := differentiableOn_kernel hz 1 d A₁ A₂ j n
  have hq := (hk.deriv (Analytic.isOpen_kernelDomain A₁ A₂ n)).div hk
    (fun x hx => kernel_ne_zero hz 1 d j n hx)
  apply hq.congr
  intro x hx
  rw [← logDeriv_kernel hz 1 d j n hx, logDeriv_apply, Pi.div_apply]

theorem kernelLogDerivative_eq_zero_iff {z : ℝ} (hz : 0 < z) (m d : ℕ)
    {A₁ A₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ Analytic.kernelDomain A₁ A₂ n) :
    kernelLogDerivative d A₁ A₂ z j n x = 0 ↔ deriv (kernel m d A₁ A₂ z j n) x = 0 := by
  rw [← logDeriv_kernel hz m d j n hx, logDeriv_apply, div_eq_zero_iff]
  simp only [kernel_ne_zero hz m d j n hx, or_false]

end ThisWork.Trajectory
