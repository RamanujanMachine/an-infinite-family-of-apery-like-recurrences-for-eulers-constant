module

public import ThisWork.LocalKernelPhase

/-! Logarithmic norm derivatives, obtained from local holomorphic logarithms. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem hasDerivAt_log_norm_comp {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0)
    {γ : ℝ → ℂ} {v : ℂ} {t : ℝ} (hγ : HasDerivAt γ v t) (ht : γ t ∈ U) :
    HasDerivAt (fun u => Real.log ‖f (γ u)‖) (v * logDeriv f (γ t)).re t := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU (γ t) ht
  obtain ⟨p, _, hp, he⟩ := exists_normalized_log_ball (mem_ball_self hr)
    (hf.mono hball) (fun z hz => hne z (hball hz))
  have hcomp := Neuschel.hasDerivAt_primitive_comp (hp _ (mem_ball_self hr)) hγ
  have hre : HasDerivAt (fun u => (p (γ u)).re) (v * logDeriv f (γ t)).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  apply (hre.const_add (Real.log ‖f (γ t)‖)).congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.tendsto.eventually (ball_mem_nhds (γ t) hr)] with u hu
  rw [he _ hu, norm_mul, Complex.norm_exp, Real.log_mul (norm_ne_zero_iff.mpr (hne _ ht))
    (Real.exp_ne_zero _), Real.log_exp]

end ThisWork
