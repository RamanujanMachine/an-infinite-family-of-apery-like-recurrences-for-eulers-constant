module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Analytic prerequisites for the uniform Gamma estimates in Lemma 8. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric MeasureTheory Asymptotics
open scoped Topology

/-- The nonnegative weight in Euler's finite integral approximation to Gamma. -/
noncomputable def gammaApproxWeight (n : ℕ) (t : ℝ) : ℝ := (max (1 - t / n) 0) ^ n

theorem gammaApproxWeight_nonneg (n : ℕ) (t : ℝ) : 0 ≤ gammaApproxWeight n t :=
  pow_nonneg (le_max_right _ _) _

theorem continuous_gammaApproxWeight (n : ℕ) : Continuous (gammaApproxWeight n) := by
  unfold gammaApproxWeight
  fun_prop

theorem gammaApproxWeight_eq_zero {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : (n : ℝ) ≤ t) :
    gammaApproxWeight n t = 0 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [gammaApproxWeight, max_eq_right (by rw [sub_nonpos]; exact (le_div_iff₀ hn0).mpr (by simpa using ht))]
  exact zero_pow hn

theorem gammaApproxWeight_le_exp {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    gammaApproxWeight n t ≤ Real.exp (-t) := by
  by_cases htn : t ≤ (n : ℝ)
  · rw [gammaApproxWeight, max_eq_left (sub_nonneg.mpr (div_le_one_of_le₀ htn (Nat.cast_nonneg n)))]
    exact Real.one_sub_div_pow_le_exp_neg htn
  · rw [gammaApproxWeight_eq_zero hn (not_le.mp htn).le]
    exact (Real.exp_pos _).le

theorem gammaApproxWeight_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => gammaApproxWeight n t) atTop (𝓝 (Real.exp (-t))) := by
  have hp : Tendsto (fun n : ℕ => (1 - t / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (-t))) := by
    simpa only [neg_div, ← sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-t)
  apply hp.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_ge_atTop t)] with n hn
  rw [gammaApproxWeight, max_eq_left (sub_nonneg.mpr (div_le_one_of_le₀ hn (Nat.cast_nonneg n)))]

noncomputable def gammaApproxIntegrand (n : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  (gammaApproxWeight n t : ℂ) * (t : ℂ) ^ (s - 1)

theorem norm_gammaApproxIntegrand_le {n : ℕ} (hn : n ≠ 0) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gammaApproxIntegrand n s t‖ ≤ Real.exp (-t) * t ^ (s.re - 1) := by
  rw [gammaApproxIntegrand, norm_mul, Complex.norm_of_nonneg (gammaApproxWeight_nonneg n t),
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (gammaApproxWeight_le_exp hn t) (Real.rpow_nonneg ht.le _)

theorem continuousOn_gammaApproxIntegrand (n : ℕ) (s : ℂ) :
    ContinuousOn (gammaApproxIntegrand n s) (Ioi 0) := by
  change ContinuousOn (fun t : ℝ => (gammaApproxWeight n t : ℂ) * (t : ℂ) ^ (s - 1)) (Ioi 0)
  apply ((Complex.continuous_ofReal.comp (continuous_gammaApproxWeight n)).continuousOn).fun_mul
  exact continuousOn_of_forall_continuousAt (fun t ht =>
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht)))

theorem integrableOn_gammaApproxIntegrand {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (gammaApproxIntegrand n s) (Ioi 0) :=
  (Real.GammaIntegral_convergent hs).mono'
    ((continuousOn_gammaApproxIntegrand n s).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun _ ht => norm_gammaApproxIntegrand_le hn s ht))

theorem GammaSeq_eq_integral_approx {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    Complex.GammaSeq s n = ∫ t in Ioi (0 : ℝ), gammaApproxIntegrand n s t := by
  have hsupport : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      t ∉ Ioc (0 : ℝ) (n : ℝ) → gammaApproxIntegrand n s t = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht hnot
    have hn_le : (n : ℝ) ≤ t := by
      by_contra! hlt
      exact hnot ⟨ht, hlt.le⟩
    rw [gammaApproxIntegrand, gammaApproxWeight_eq_zero hn hn_le, Complex.ofReal_zero, zero_mul]
  have hrestriction : (∫ t in Ioc (0 : ℝ) (n : ℝ), gammaApproxIntegrand n s t) =
      ∫ t in Ioi (0 : ℝ), gammaApproxIntegrand n s t := by
    simpa only [Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self] using
      setIntegral_eq_integral_of_ae_compl_eq_zero hsupport
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (Nat.cast_nonneg n), ← hrestriction]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [gammaApproxIntegrand, gammaApproxWeight,
    max_eq_left (sub_nonneg.mpr (div_le_one_of_le₀ ht.2 (Nat.cast_nonneg n)))]

/-- Euler's approximants obey a bound independent of the approximation index
and of the imaginary part. This provides the local analytic domination. -/
theorem norm_GammaSeq_le {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.GammaSeq s n‖ ≤ Real.Gamma s.re := by
  rw [GammaSeq_eq_integral_approx hn hs, Real.Gamma_eq_integral hs]
  exact norm_integral_le_of_norm_le (Real.GammaIntegral_convergent hs)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun _ ht => norm_gammaApproxIntegrand_le hn s ht))

theorem norm_Gamma_le {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  apply le_of_tendsto (continuous_norm.tendsto _ |>.comp (Complex.GammaSeq_tendsto_Gamma s))
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  exact norm_GammaSeq_le hn hs

/-- A scalar error controlling the complex Euler approximants on vertical strips. -/
noncomputable def gammaApproxError (n : ℕ) (a t : ℝ) : ℝ :=
  (Real.exp (-t) - gammaApproxWeight (n + 1) t) * t ^ (a - 1)

theorem gammaApproxError_bounds (n : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ gammaApproxError n a t ∧ gammaApproxError n a t ≤ Real.exp (-t) * t ^ (a - 1) := by
  constructor
  · exact mul_nonneg (sub_nonneg.mpr (gammaApproxWeight_le_exp (Nat.succ_ne_zero n) t))
      (Real.rpow_nonneg ht.le _)
  · exact mul_le_mul_of_nonneg_right
      (sub_le_self _ (gammaApproxWeight_nonneg (n + 1) t)) (Real.rpow_nonneg ht.le _)

theorem continuousOn_gammaApproxError (n : ℕ) (a : ℝ) :
    ContinuousOn (gammaApproxError n a) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun t : ℝ => (Real.exp (-t) - gammaApproxWeight (n + 1) t) * t ^ (a - 1)) t
  exact ((Real.continuous_exp.continuousAt.comp continuousAt_id.neg).sub
    (continuous_gammaApproxWeight (n + 1)).continuousAt).mul
      (Real.continuousAt_rpow_const t (a - 1) (Or.inl (ne_of_gt ht)))

theorem integrableOn_gammaApproxError (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (gammaApproxError n a) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent ha).mono'
    ((continuousOn_gammaApproxError n a).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (gammaApproxError_bounds n a ht).1] using
    (gammaApproxError_bounds n a ht).2

theorem gammaApproxError_integral_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∫ t in Ioi (0 : ℝ), gammaApproxError n a t) atTop (𝓝 0) := by
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), Tendsto (fun n => gammaApproxError n a t) atTop (𝓝 0) := by
    intro t ht
    have h := (gammaApproxWeight_tendsto t).comp (tendsto_add_atTop_nat 1)
    simpa only [gammaApproxError, Function.comp_def, sub_self, zero_mul] using
      ((tendsto_const_nhds (x := Real.exp (-t))).sub h).mul_const (t ^ (a - 1))
  have hbound : ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖gammaApproxError n a t‖ ≤ Real.exp (-t) * t ^ (a - 1) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (gammaApproxError_bounds n a ht).1] using
      (gammaApproxError_bounds n a ht).2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun t : ℝ => Real.exp (-t) * t ^ (a - 1))
    (fun n => (integrableOn_gammaApproxError n ha).aestronglyMeasurable)
    (Real.GammaIntegral_convergent ha) hbound
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hpoint t ht))

theorem rpow_le_endpoint_sum {t a b u : ℝ} (ht : 0 < t) (ha : a ≤ u) (hb : u ≤ b) :
    t ^ u ≤ t ^ a + t ^ b := by
  by_cases ht1 : t ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge ht ht1 ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le (not_le.mp ht1).le hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

theorem norm_gammaApproxIntegrand_sub_le (n : ℕ) {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) {t : ℝ} (ht : 0 < t) :
    ‖gammaApproxIntegrand (n + 1) s t - (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s - 1)‖ ≤
      gammaApproxError n a t + gammaApproxError n b t := by
  have hδ : 0 ≤ Real.exp (-t) - gammaApproxWeight (n + 1) t :=
    sub_nonneg.mpr (gammaApproxWeight_le_exp (Nat.succ_ne_zero n) t)
  have heq : gammaApproxIntegrand (n + 1) s t - (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s - 1) =
      -((Real.exp (-t) - gammaApproxWeight (n + 1) t : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) := by
    simp only [gammaApproxIntegrand, Complex.ofReal_sub]
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_of_nonneg hδ,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  change _ ≤ (Real.exp (-t) - gammaApproxWeight (n + 1) t) * t ^ (a - 1) +
    (Real.exp (-t) - gammaApproxWeight (n + 1) t) * t ^ (b - 1)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (rpow_le_endpoint_sum ht (by linarith) (by linarith)) hδ

/-- A uniform error bound on a whole closed vertical strip in the right
half-plane. Its two scalar bounds tend to zero. -/
theorem norm_GammaSeq_sub_le (n : ℕ) {a b : ℝ} (ha : 0 < a) {s : ℂ}
    (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖Complex.GammaSeq s (n + 1) - Complex.Gamma s‖ ≤
      (∫ t in Ioi (0 : ℝ), gammaApproxError n a t) +
      ∫ t in Ioi (0 : ℝ), gammaApproxError n b t := by
  have hs : 0 < s.re := ha.trans_le hsa
  have hb : 0 < b := hs.trans_le hsb
  rw [GammaSeq_eq_integral_approx (Nat.succ_ne_zero n) hs, Complex.Gamma_eq_integral hs,
    Complex.GammaIntegral, ← integral_sub (integrableOn_gammaApproxIntegrand (Nat.succ_ne_zero n) hs)
      (Complex.GammaIntegral_convergent hs)]
  have h := norm_integral_le_of_norm_le ((integrableOn_gammaApproxError n ha).add (integrableOn_gammaApproxError n hb))
    ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => norm_gammaApproxIntegrand_sub_le n hsa hsb ht))
  simpa only [Pi.add_apply, integral_add (integrableOn_gammaApproxError n ha) (integrableOn_gammaApproxError n hb)] using h

theorem GammaSeq_tendsto_uniform_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn (fun n : ℕ => fun s : ℂ => Complex.GammaSeq s (n + 1))
      Complex.Gamma atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : Tendsto (fun n => (∫ t in Ioi (0 : ℝ), gammaApproxError n a t) +
      ∫ t in Ioi (0 : ℝ), gammaApproxError n b t) atTop (𝓝 0) := by
    simpa only [add_zero] using (gammaApproxError_integral_tendsto ha).add
      (gammaApproxError_integral_tendsto (ha.trans_le hab))
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn s hs
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_GammaSeq_sub_le n ha hs.1 hs.2).trans_lt hn

/-- Euler's Gamma approximants converge locally uniformly on the open right
half-plane. Consequently their complex derivatives can be passed to the limit. -/
theorem GammaSeq_tendsto_locally_uniform :
    TendstoLocallyUniformlyOn (fun n : ℕ => fun s : ℂ => Complex.GammaSeq s (n + 1))
      Complex.Gamma atTop {s : ℂ | 0 < s.re} := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε s hs
  let U : Set ℂ := {z | s.re / 2 < z.re ∧ z.re < s.re + 1}
  have hs0 : 0 < s.re := hs
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hsU : s ∈ U := ⟨half_lt_self hs0, lt_add_one _⟩
  refine ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hsU), ?_⟩
  have hu := Metric.tendstoUniformlyOn_iff.mp
    (GammaSeq_tendsto_uniform_strip (half_pos hs0) (show s.re / 2 ≤ s.re + 1 by linarith)) ε hε
  exact hu.mono (fun n hn z hz => hn z ⟨hz.1.le, hz.2.le⟩)

end ThisWork
