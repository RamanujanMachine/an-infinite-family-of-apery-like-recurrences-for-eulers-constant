module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Laplace moments for complex scaling in the open right half-plane. -/

@[expose] public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable def momentKernel (s : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (t ^ (s - 1) : ℝ) * Complex.exp (-z * (t : ℂ))

theorem norm_momentKernel (s : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖momentKernel s z t‖ = t ^ (s - 1) * Real.exp (-z.re * t) := by
  simp [momentKernel, Complex.norm_exp, abs_of_nonneg (Real.rpow_nonneg ht.le _)]

theorem continuousOn_momentKernel (s : ℝ) (z : ℂ) :
    ContinuousOn (momentKernel s z) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))).mul
    ((show Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ))) by fun_prop).continuousOn)

theorem integrableOn_momentKernel {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (momentKernel s z) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-z.re * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (by linarith : -1 < s - 1) zero_lt_one hz
  exact hb.mono' ((continuousOn_momentKernel s z).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => (norm_momentKernel s z ht).le))

theorem hasDerivAt_momentKernel (s : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => momentKernel s w t) (-(t : ℂ) * momentKernel s z t) z := by
  simpa [momentKernel, mul_comm, mul_left_comm, mul_assoc] using
    ((((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp).const_mul ((t ^ (s - 1) : ℝ) : ℂ))

theorem norm_momentKernel_derivative (s : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖-(t : ℂ) * momentKernel s z t‖ = t ^ s * Real.exp (-z.re * t) := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    norm_momentKernel s z ht, ← mul_assoc, Real.rpow_sub ht, Real.rpow_one]
  rw [mul_div_cancel₀ _ (ne_of_gt ht)]

theorem differentiableAt_laplaceMoment {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w => ∫ t : ℝ in Ioi 0, momentKernel s w t) z := by
  have hnb : {w : ℂ | z.re / 2 < w.re} ∈ 𝓝 z :=
    Complex.continuous_re.continuousAt.preimage_mem_nhds (lt_mem_nhds (half_lt_self hz))
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ w : ℂ, z.re / 2 < w.re →
      ‖-(t : ℂ) * momentKernel s w t‖ ≤ t ^ s * Real.exp (-(z.re / 2) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    simpa only [norm_momentKernel_derivative s w ht] using
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hw.le) ht.le))
        (Real.rpow_nonneg ht.le s)
  have hb : IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-(z.re / 2) * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (by linarith : -1 < s) zero_lt_one (half_pos hz)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hnb
    (Eventually.of_forall (fun w => (continuousOn_momentKernel s w).aestronglyMeasurable measurableSet_Ioi))
    (integrableOn_momentKernel hs hz)
    ((Complex.continuous_ofReal.neg.continuousOn.mul (continuousOn_momentKernel s z)).aestronglyMeasurable
      measurableSet_Ioi) hbound hb
    (Eventually.of_forall (fun t w _ => hasDerivAt_momentKernel s w t))).2.differentiableAt

theorem laplaceMoment_ofReal {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, momentKernel s (r : ℂ) t) =
      (r : ℂ) ^ (-(s : ℂ)) * (Real.Gamma s : ℂ) := by
  have hR := congrArg Complex.ofReal (Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr)
  refine Eq.trans ?_ (hR.trans ?_)
  · refine (setIntegral_congr_fun measurableSet_Ioi ?_).trans
      (Complex.ofRealLI.integral_comp_comm (fun t : ℝ => t ^ (s - 1) * Real.exp (-(r * t))))
    intro t _
    simp [momentKernel, Complex.ofRealLI_apply]
  · simp only [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le,
      Complex.ofReal_mul, Complex.ofReal_cpow hr.le, Complex.ofReal_neg]

/-- Euler's Laplace integral for complex scaling in the open right half-plane. -/
theorem laplaceMoment_eq_gamma {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, momentKernel s z t) = z ^ (-(s : ℂ)) * (Real.Gamma s : ℂ) := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ (fun w => ∫ t : ℝ in Ioi 0, momentKernel s w t) {w : ℂ | 0 < w.re} :=
    (show DifferentiableOn ℂ (fun w => ∫ t : ℝ in Ioi 0, momentKernel s w t) {w : ℂ | 0 < w.re}
      from fun w hw => (differentiableAt_laplaceMoment hs hw).differentiableWithinAt).analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (-(s : ℂ)) * (Real.Gamma s : ℂ)) {w : ℂ | 0 < w.re} :=
    (show DifferentiableOn ℂ (fun w : ℂ => w ^ (-(s : ℂ)) * (Real.Gamma s : ℂ)) {w : ℂ | 0 < w.re}
      from fun w hw => ((differentiableAt_id.cpow_const (Or.inl hw)).mul_const _).differentiableWithinAt)
      |>.analyticOnNhd hU
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
      ((show ∀ᶠ r : ℝ in 𝓝[>] 1, 1 < r from self_mem_nhdsWithin).mono (fun r hr => by
        change (r : ℂ) ≠ 1
        exact_mod_cast ne_of_gt hr))
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] 1,
      (∫ t : ℝ in Ioi 0, momentKernel s w t) = w ^ (-(s : ℂ)) * (Real.Gamma s : ℂ) :=
    ht.frequently (((show ∀ᶠ r : ℝ in 𝓝[>] 1, 1 < r from self_mem_nhdsWithin).mono
      (fun r hr => laplaceMoment_ofReal hs (zero_lt_one.trans hr))).frequently)
  exact hF.eqOn_of_preconnected_of_frequently_eq hG (convex_halfSpace_re_gt 0).isPreconnected
    (by simp) hfreq hz

theorem cpow_pos_scale {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz),
    Complex.log_ofReal_mul hr hz, Complex.ofReal_log hr.le, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.cpow_def_of_ne_zero hz]

theorem scaled_laplaceMoment_eq_gamma {s n : ℝ} (hs : 0 < s) (hn : 0 < n)
    {z : ℂ} (hz : 0 < z.re) :
    z ^ (s : ℂ) * (∫ t : ℝ in Ioi 0, momentKernel s ((n : ℂ) * z) t) =
      ((Real.Gamma s / n ^ s : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero (Or.inl hz)
  rw [laplaceMoment_eq_gamma hs (by simpa using mul_pos hn hz), cpow_pos_scale hn hz0,
    Complex.cpow_neg, Complex.cpow_neg]
  simp [mul_comm, mul_assoc, Complex.cpow_ne_zero_iff.mpr (Or.inl hz0),
    ← Complex.ofReal_cpow hn.le, div_eq_mul_inv]

/-- Uniform exponential domination of the omitted part of a complex Laplace ray. -/
theorem momentKernel_tail_le (s : ℝ) {n η t : ℝ} {z : ℂ}
    (hn : 1 ≤ n) (hη : 0 < η) (hz : η ≤ z.re) (ht : 1 ≤ t) :
    ‖momentKernel s ((n : ℂ) * z) t‖ ≤
      Real.exp (-(n - 1) * η) * (t ^ (s - 1) * Real.exp (-η * t)) := by
  have he : -(n * z.re) * t ≤ -(n - 1) * η + -η * t := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ n) (by linarith : 0 ≤ t)) (sub_nonneg.mpr hz),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr ht)) hη.le]
  simpa only [norm_momentKernel s _ (lt_of_lt_of_le zero_lt_one ht), Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Real.exp_add,
    mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.rpow_nonneg (by linarith) (s - 1))

/-- The Gamma approximation on a finite ray has an exponentially small error,
uniformly over every closed sub-half-plane `η ≤ Re z`. -/
theorem uniform_incomplete_laplace_moment {s η : ℝ} (hs : 0 < s) (hη : 0 < η) :
    ∃ C ≥ 0, ∀ n : ℝ, 1 ≤ n → ∀ z : ℂ, η ≤ z.re →
      ‖(∫ t : ℝ in 0..1, momentKernel s ((n : ℂ) * z) t) -
        ((n : ℂ) * z) ^ (-(s : ℂ)) * (Real.Gamma s : ℂ)‖ ≤
        C * Real.exp (-(n - 1) * η) := by
  let g : ℝ → ℝ := fun t => t ^ (s - 1) * Real.exp (-η * t)
  have hg : IntegrableOn g (Ioi 1) :=
    (show IntegrableOn g (Ioi 0) from by
      simpa only [g, Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (by linarith : -1 < s - 1) zero_lt_one hη).mono_set
          (Ioi_subset_Ioi zero_le_one)
  refine ⟨∫ t : ℝ in Ioi 1, g t, integral_nonneg_of_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht =>
      mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans ht).le _) (Real.exp_nonneg _))), ?_⟩
  intro n hn z hz
  have hRe : 0 < ((n : ℂ) * z).re := by
    simpa using mul_pos (lt_of_lt_of_le zero_lt_one hn) (hη.trans_le hz)
  have heq := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_momentKernel hs hRe) zero_le_one
  rw [← heq, laplaceMoment_eq_gamma hs hRe, sub_sub_cancel_left, norm_neg]
  simpa only [integral_const_mul, integral_mul_const, mul_comm] using
    norm_integral_le_of_norm_le (hg.const_mul (Real.exp (-(n - 1) * η)))
      ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => momentKernel_tail_le s hn hη hz ht.le))

/-- After the ray factor cancels, the coefficient is `Γ(s) / n^s`, independently
of the endpoint. The finite-ray error remains uniform on compact parameter families. -/
theorem uniform_scaled_incomplete_laplace_moment {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {s η : ℝ} (hs : 0 < s) (hη : 0 < η) {α : Z → ℂ} (hα : Continuous α)
    (hgap : ∀ z, η ≤ (α z).re) :
    ∃ C ≥ 0, ∀ n : ℝ, 1 ≤ n → ∀ z,
      ‖α z ^ (s : ℂ) * (∫ t : ℝ in 0..1, momentKernel s ((n : ℂ) * α z) t) -
        ((Real.Gamma s / n ^ s : ℝ) : ℂ)‖ ≤ C * Real.exp (-(n - 1) * η) := by
  obtain ⟨C, hC0, hC⟩ := uniform_incomplete_laplace_moment hs hη
  have hp : Continuous (fun z => α z ^ (s : ℂ)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (continuousAt_cpow_const (Or.inl (hη.trans_le (hgap z)))).comp hα.continuousAt)
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hp.continuousOn
  refine ⟨max R 0 * C, mul_nonneg (le_max_right _ _) hC0, fun n hn z => ?_⟩
  rw [← scaled_laplaceMoment_eq_gamma hs (lt_of_lt_of_le zero_lt_one hn) (hη.trans_le (hgap z)),
    ← mul_sub, norm_mul, laplaceMoment_eq_gamma hs
      (by simpa using mul_pos (lt_of_lt_of_le zero_lt_one hn) (hη.trans_le (hgap z)))]
  exact (mul_le_mul ((hR z (mem_univ z)).trans (le_max_left R 0)) (hC n hn (α z) (hgap z))
    (norm_nonneg _) (le_max_right R 0)).trans_eq (mul_assoc _ _ _).symm

end Neuschel
