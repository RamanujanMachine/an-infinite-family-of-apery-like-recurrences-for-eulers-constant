module

public import Neuschel.Theorem
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Bridges between the published hypotheses and the parameterized formalization. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

/-- The continuous extension of the first smooth piece's velocity supplies the
one-sided tangent at the starting point, as assumed in Neuschel's path definition. -/
theorem endpoint_tangent_of_smooth_piece {γ velocity : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hγ : ContinuousOn γ (Icc 0 L)) (hv : ContinuousOn velocity (Icc 0 L))
    (hd : ∀ s ∈ Ioo 0 L, HasDerivAt γ (velocity s) s) :
    HasDerivWithinAt γ (velocity 0) (Ici 0) 0 := by
  have hnear : Ioo (0 : ℝ) L ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hL
  have hvlim : Tendsto velocity (𝓝[>] 0) (𝓝 (velocity 0)) :=
    ((hv 0 ⟨le_rfl, hL.le⟩).mono Ioo_subset_Icc_self).tendsto.mono_left
      (nhdsWithin_le_of_mem hnear)
  have hderivlim : Tendsto (deriv γ) (𝓝[>] 0) (𝓝 (velocity 0)) :=
    hvlim.congr' (Filter.Eventually.mono hnear (fun s hs => (hd s hs).deriv.symm))
  exact hasDerivWithinAt_Ici_of_tendsto_deriv (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) ((hγ 0 ⟨le_rfl, hL.le⟩).mono Ioo_subset_Icc_self) hnear hderivlim

/-- The argument of the leading coefficient specified in part (i) of the paper.
The tangent argument `ω` may be any real lift. -/
noncomputable def paperLeadingArg (μ : ℕ) (v b : ℂ) (ω : ℝ) : ℝ :=
  Complex.arg (b * v ^ μ) - (μ : ℝ) * ω

/-- The implemented root is exactly Neuschel's logarithmic branch, for every
choice of the lifted outgoing tangent argument. -/
theorem leadingRoot_eq_paper_branch {μ : ℕ} (hμ : μ ≠ 0) {v b : ℂ}
    (hv : v ≠ 0) (hb : b ≠ 0) {ω : ℝ}
    (hω : v = (‖v‖ : ℂ) * Complex.exp ((ω : ℂ) * Complex.I)) :
    leadingRoot μ v b = Complex.exp (((Real.log ‖b‖ : ℂ) +
      (paperLeadingArg μ v b ω : ℂ) * Complex.I) / (μ : ℂ)) := by
  have hlog : Complex.log (b * v ^ μ) = (Real.log ‖b‖ : ℂ) +
      (μ : ℂ) * (Real.log ‖v‖ : ℂ) + (Complex.arg (b * v ^ μ) : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (Complex.log (b * v ^ μ)), Complex.log_re, Complex.log_im,
      norm_mul, norm_pow, Real.log_mul (norm_ne_zero_iff.mpr hb)
        (pow_ne_zero μ (norm_ne_zero_iff.mpr hv)), Real.log_pow]
    push_cast
    ring
  have he : Complex.log (b * v ^ μ) / (μ : ℂ) =
      ((Real.log ‖b‖ : ℂ) + (paperLeadingArg μ v b ω : ℂ) * Complex.I) / (μ : ℂ) +
        ((Real.log ‖v‖ : ℂ) + (ω : ℂ) * Complex.I) := by
    rw [hlog, paperLeadingArg]
    push_cast
    field_simp
    ring
  have hvexp : Complex.exp ((Real.log ‖v‖ : ℂ) + (ω : ℂ) * Complex.I) = v := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hv)]
    exact hω.symm
  rw [leadingRoot, normalizedRoot, he, Complex.exp_add, hvexp, mul_div_cancel_right₀ _ hv]

/-- The lifted coefficient argument is an argument of `b` and satisfies exactly
Neuschel's half-plane constraint `|ω₀ + μ ω| ≤ π/2`. -/
theorem paperLeadingArg_spec {μ : ℕ} (hμ : μ ≠ 0) {v b : ℂ}
    (hv : v ≠ 0) (hb : b ≠ 0) {ω : ℝ}
    (hω : v = (‖v‖ : ℂ) * Complex.exp ((ω : ℂ) * Complex.I))
    (hsector : 0 ≤ (b * v ^ μ).re) :
    Complex.exp ((Real.log ‖b‖ : ℂ) + (paperLeadingArg μ v b ω : ℂ) * Complex.I) = b ∧
      |paperLeadingArg μ v b ω + (μ : ℝ) * ω| ≤ Real.pi / 2 := by
  have hp := leadingRoot_pow hμ hv hb
  rw [leadingRoot_eq_paper_branch hμ hv hb hω, ← Complex.exp_nat_mul,
    mul_comm (μ : ℂ), div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hμ)] at hp
  exact ⟨hp, by simpa only [paperLeadingArg, sub_add_cancel] using
    Complex.abs_arg_le_pi_div_two_iff.mpr hsector⟩

/-- The paper's absolute contour-integral weight is exactly the norm of the
parameterized complex integrand. -/
theorem norm_contour_integrand (n : ℝ) (p q velocity : ℂ) :
    ‖Complex.exp (-(n : ℂ) * p) * q * velocity‖ =
      Real.exp (-n * p.re) * ‖q‖ * ‖velocity‖ := by
  simp [Complex.norm_exp, Complex.mul_re]

/-- The restricted integral used in the formalization is the usual improper
limit of contour-parameter integrals at the excluded final endpoint. -/
theorem tendsto_truncated_integral {f : ℝ → ℂ} (hf : IntegrableOn f (Ioo 0 1)) :
    Tendsto (fun r : ℝ => ∫ s in 0..r, f s) (𝓝[<] 1)
      (𝓝 (∫ s in Ioo (0 : ℝ) 1, f s)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ := volume) zero_le_one).mpr hf
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)
  have hc1 : ContinuousWithinAt (fun r : ℝ => ∫ s in 0..r, f s) (Ioo 0 1) 1 :=
    (hc 1 right_mem_uIcc).mono (by simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] using
    hc1.tendsto.mono_left (nhdsWithin_le_of_mem (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)))

theorem UniformLaplaceExpansion.improper_convergence {Z : Type*} [TopologicalSpace Z]
    {μ k : ℕ} {P q : ℂ → Z → ℂ} {a v : ℂ} {b c : ℕ → Z → ℂ}
    {γ velocity : ℝ → ℂ} {N : ℝ}
    (E : UniformLaplaceExpansion μ k P q a v b c γ velocity N) {n : ℕ} (hn : N ≤ (n : ℝ)) (z : Z) :
    Tendsto (fun r : ℝ => ∫ s in 0..r,
      Complex.exp (-(n : ℂ) * P (γ s) z) * (velocity s * q (γ s) z)) (𝓝[<] 1)
      (𝓝 (∫ s in Ioo (0 : ℝ) 1,
        Complex.exp (-(n : ℂ) * P (γ s) z) * (velocity s * q (γ s) z))) :=
  tendsto_truncated_integral (E.absolute_convergence n hn z)

/-- Replacing the nonnegative vanishing order by the paper's positive `λ`
gives exactly its Gamma indices and powers of the Laplace parameter. -/
theorem paper_exponent {ℓ : ℕ} (hℓ : 0 < ℓ) (j : ℕ) :
    (((j + (ℓ - 1) : ℕ) : ℝ) + 1) = ((j + ℓ : ℕ) : ℝ) := by
  norm_cast
  omega

/-- The uniform big-O statement with an explicit integer threshold, both
independent of the parameter, and with the paper's positive exponent `λ`. -/
theorem UniformLaplaceExpansion.paper_remainder {Z : Type*} [TopologicalSpace Z]
    {μ ℓ : ℕ} {P q : ℂ → Z → ℂ} {a v : ℂ} {b c : ℕ → Z → ℂ}
    {γ velocity : ℝ → ℂ} {N : ℝ}
    (E : UniformLaplaceExpansion μ (ℓ - 1) P q a v b c γ velocity N) (hℓ : 0 < ℓ) (m : ℕ) :
    ∃ C ≥ 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ z,
      ‖E.remainder m n z‖ ≤ C * (n : ℝ) ^ (-(((m + ℓ : ℕ) : ℝ) / (μ : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := E.remainder_bound m
  refine ⟨C, hC, ?_⟩
  simpa only [paper_exponent hℓ m] using eventually_atTop.mp hb

/-- Both displayed coefficients, with precisely the paper's positive exponent. -/
theorem UniformLaplaceExpansion.paper_coefficients {Z : Type*} [TopologicalSpace Z]
    {μ ℓ : ℕ} {P q : ℂ → Z → ℂ} {a v : ℂ} {b c : ℕ → Z → ℂ}
    {γ velocity : ℝ → ℂ} {N : ℝ}
    (E : UniformLaplaceExpansion μ (ℓ - 1) P q a v b c γ velocity N) (hℓ : 0 < ℓ) (z : Z) :
    E.coefficient 0 z = c 0 z / ((μ : ℂ) * leadingRoot μ v (b 0 z) ^ ℓ) ∧
      E.coefficient 1 z =
        (c 1 z / (μ : ℂ) - ((ℓ + 1 : ℕ) : ℂ) * b 1 z * c 0 z / ((μ : ℂ) ^ 2 * b 0 z)) /
          leadingRoot μ v (b 0 z) ^ (ℓ + 1) := by
  have hpow : ℓ - 1 + 2 = ℓ + 1 := by omega
  have hcast : ((ℓ - 1 : ℕ) : ℂ) + 2 = ((ℓ + 1 : ℕ) : ℂ) := by exact_mod_cast hpow
  exact ⟨by simpa only [Nat.sub_add_cancel hℓ] using E.coefficient_zero z,
    by simpa only [hpow, hcast] using E.coefficient_one_paper_form z⟩

/-- The expansion with the published Gamma indices and powers of `n`. -/
theorem UniformLaplaceExpansion.paper_expansion {Z : Type*} [TopologicalSpace Z]
    {μ ℓ : ℕ} {P q : ℂ → Z → ℂ} {a v : ℂ} {b c : ℕ → Z → ℂ}
    {γ velocity : ℝ → ℂ} {N : ℝ}
    (E : UniformLaplaceExpansion μ (ℓ - 1) P q a v b c γ velocity N) (hℓ : 0 < ℓ) (m n : ℕ) (z : Z) :
    (∫ s in Ioo (0 : ℝ) 1, Complex.exp (-(n : ℂ) * P (γ s) z) * (velocity s * q (γ s) z)) =
      Complex.exp (-(n : ℂ) * P a z) *
        ((∑ j ∈ Finset.range m, E.coefficient j z *
          ((Real.Gamma (((j + ℓ : ℕ) : ℝ) / (μ : ℝ)) /
            (n : ℝ) ^ (((j + ℓ : ℕ) : ℝ) / (μ : ℝ)) : ℝ) : ℂ)) + E.remainder m n z) := by
  simpa only [paper_exponent hℓ] using E.expansion m n z

end Neuschel
