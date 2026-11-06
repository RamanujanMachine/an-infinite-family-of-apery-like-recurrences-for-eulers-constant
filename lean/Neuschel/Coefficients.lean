module

public import Neuschel.LocalContour
public import Neuschel.Amplitude

/-! The first two coefficients of the transformed amplitude. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

theorem phaseQuotient_succ_center {Z : Type*} (k : ℕ) (a : ℂ) (q : ℂ → Z → ℂ) (z : Z) :
    phaseQuotient (k + 1) a q a z = deriv (fun t => phaseQuotient k a q t z) a := by
  simp only [phaseQuotient, Function.iterate_succ_apply', Function.swap, dslope_same]

theorem deriv_phaseQuotient_center_of_expansion {Z : Type*} (k : ℕ) {a : ℂ}
    {q : ℂ → Z → ℂ} {c : ℕ → Z → ℂ} {z : Z}
    (hs : ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z)) :
    deriv (fun t => phaseQuotient k a q t z) a = c 1 z := by
  rw [← phaseQuotient_succ_center]
  simpa only [FormalMultilinearSeries.coeff_ofScalars, Nat.add_comm k 1, shiftedCoefficients_add] using
    phaseQuotient_center_eq_coeff (k + 1) (hasFPowerSeriesAt_of_shifted_expansion hs)

theorem analytic_factor_eq_quotient {Z : Type*} (k : ℕ) {a : ℂ}
    {q h : ℂ → Z → ℂ} {c : ℕ → Z → ℂ} {z : Z}
    (hs : ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z))
    (hc : c 0 z ≠ 0) (hcenter : h a z = 1) {t : ℂ}
    (hfactor : q t z = c 0 z * (t - a) ^ k * h t z) :
    h t z = phaseQuotient k a q t z / c 0 z := by
  by_cases ht : t = a
  · simp only [ht, hcenter, phaseQuotient_center_of_expansion k hs, div_self hc]
  · have hpow := pow_ne_zero k (sub_ne_zero.mpr ht)
    have heq := eq_pow_mul_phaseQuotient_of_expansion k hs t
    apply (eq_div_iff hc).mpr
    apply mul_left_cancel₀ hpow
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hfactor.symm.trans heq

theorem hasDerivAt_analytic_factor {Z : Type*} (k : ℕ) {a : ℂ}
    {q h : ℂ → Z → ℂ} {c : ℕ → Z → ℂ} {z : Z}
    (hs : ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z))
    (hc : c 0 z ≠ 0) (hcenter : h a z = 1)
    (hfactor : ∀ᶠ t in 𝓝 a, q t z = c 0 z * (t - a) ^ k * h t z) :
    HasDerivAt (fun t => h t z) (c 1 z / c 0 z) a := by
  have hd := (hasFPowerSeriesAt_of_shifted_expansion hs).has_fpower_series_iterate_dslope_fslope k
  have hdq : DifferentiableAt ℂ (fun t => phaseQuotient k a q t z) a := hd.differentiableAt
  have hq : HasDerivAt (fun t => phaseQuotient k a q t z) (c 1 z) a := by
    simpa only [deriv_phaseQuotient_center_of_expansion k hs] using hdq.hasDerivAt
  exact (hq.div_const (c 0 z)).congr_of_eventuallyEq
    (hfactor.mono (fun t ht => analytic_factor_eq_quotient k hs hc hcenter ht))

theorem hasDerivAt_normalizedRoot_one (μ : ℕ) :
    HasDerivAt (normalizedRoot μ) ((μ : ℂ)⁻¹) 1 := by
  convert ((Complex.hasDerivAt_log Complex.one_mem_slitPlane).div_const (μ : ℂ)).cexp using 1
  · rfl
  · simp

/-- Second derivative of a coordinate with a simple zero, expressed through
its analytic unit factor. -/
theorem hasDerivAt_deriv_simple_factor {U : Set ℂ} (hU : IsOpen U) {a β : ℂ} (ha : a ∈ U)
    {r : ℂ → ℂ} (hr : DifferentiableOn ℂ r U) :
    HasDerivAt (deriv (fun t => β * ((t - a) * r t))) (2 * β * deriv r a) a := by
  have heq : deriv (fun t => β * ((t - a) * r t)) =ᶠ[𝓝 a]
      (fun t => β * (r t + (t - a) * deriv r t)) := by
    filter_upwards [hU.mem_nhds ha] with t ht
    simpa only [one_mul, id_eq, Pi.mul_def] using
      ((((hasDerivAt_id t).sub_const a).mul
        ((hr.differentiableAt (hU.mem_nhds ht)).hasDerivAt)).const_mul β).deriv
  have h := (((hr.differentiableAt (hU.mem_nhds ha)).hasDerivAt).fun_add
    (((hasDerivAt_id a).sub_const a).mul
      (((hr.deriv hU).differentiableAt (hU.mem_nhds ha)).hasDerivAt))).const_mul β
  have h' : HasDerivAt (fun t => β * (r t + (t - a) * deriv r t))
      (2 * β * deriv r a) a := by
    simpa [Pi.mul_def, id_eq, mul_comm, mul_left_comm, mul_assoc, ← two_mul] using h
  exact h'.congr_of_eventuallyEq heq

theorem LocalInverseFamily.hasDerivAt_deriv_inverse_center {Z : Type*} [TopologicalSpace Z]
    {p : ℂ → Z → ℂ} {a : ℂ} {G : Set ℂ} (e : LocalInverseFamily p a G)
    (hz : ∀ z, p a z = 0) {β : Z → ℂ}
    (hβ : ∀ z, HasDerivAt (fun t => p t z) (β z) a) (hβ0 : ∀ z, β z ≠ 0)
    {z : Z} {p₂ : ℂ} (h₂ : HasDerivAt (deriv (fun t => p t z)) p₂ a) :
    HasDerivAt (deriv (fun w => e.inverse w z)) (-p₂ / β z ^ 3) 0 := by
  have hT : HasDerivAt (fun w => e.inverse w z) ((β z)⁻¹) 0 := by
    simpa only [e.inverse_center hz z, (hβ z).deriv] using
      e.hasDerivAt_inverse_on_source e.differentiableOn_sourceBall (mem_ball_self e.targetRadius_pos) z
  have heq : deriv (fun w => e.inverse w z) =ᶠ[𝓝 0]
      (fun w => (deriv (fun t => p t z) (e.inverse w z))⁻¹) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) e.targetRadius_pos] with w hw
    exact (e.hasDerivAt_inverse_on_source e.differentiableOn_sourceBall hw z).deriv
  have hc : HasDerivAt (fun w => deriv (fun t => p t z) (e.inverse w z))
      (p₂ * (β z)⁻¹) 0 := by
    simpa only [Function.comp_def, e.inverse_center hz z] using
      ((show HasDerivAt (deriv (fun t => p t z)) p₂ (e.inverse 0 z) from
        by simpa only [e.inverse_center hz z] using h₂).comp 0 hT)
  have hi := hc.inv (show deriv (fun t => p t z) (e.inverse 0 z) ≠ 0 from by
    simpa only [e.inverse_center hz z, (hβ z).deriv] using hβ0 z)
  have hi' : HasDerivAt (fun w => (deriv (fun t => p t z) (e.inverse w z))⁻¹)
      (-p₂ / β z ^ 3) 0 := hi.congr_deriv (by
    rw [e.inverse_center hz z, (hβ z).deriv]
    field_simp)
  exact hi'.congr_of_eventuallyEq heq

theorem deriv_dslope_center {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    {T : ℂ → ℂ} (hT : DifferentiableOn ℂ T U) {d₂ : ℂ}
    (h₂ : HasDerivAt (deriv T) d₂ 0) :
    deriv (dslope T 0) 0 = d₂ / 2 := by
  have hD : DifferentiableOn ℂ (dslope T 0) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds h0)).mpr hT
  have h := hasDerivAt_deriv_simple_factor (β := (1 : ℂ)) hU h0 hD
  have heq : (fun t : ℂ => 1 * ((t - 0) * dslope T 0 t)) = fun t => T t - T 0 := by
    funext t
    simpa only [one_mul, sub_zero, smul_eq_mul] using sub_smul_dslope T 0 t
  rw [heq] at h
  have h' : HasDerivAt (deriv T) (2 * deriv (dslope T 0) 0) 0 := by
    simpa only [deriv_sub_const_fun, mul_one] using h
  have hval := h'.unique h₂
  linear_combination hval / 2

theorem hasDerivAt_transformed_factor {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    {T g : ℂ → ℂ} (hT : DifferentiableOn ℂ T U) {a d d₂ g₁ : ℂ}
    (hTa : T 0 = a) (h₁ : HasDerivAt T d 0) (h₂ : HasDerivAt (deriv T) d₂ 0)
    (hg : HasDerivAt g g₁ a) (k : ℕ) :
    HasDerivAt (fun w => dslope T 0 w ^ k * (g (T w) * deriv T w))
      ((k : ℂ) * d ^ (k - 1) * (d₂ / 2) * (g a * d) +
        d ^ k * (g₁ * d * d + g a * d₂)) 0 := by
  have hD : HasDerivAt (dslope T 0) (d₂ / 2) 0 := by
    rw [← deriv_dslope_center hU h0 hT h₂]
    exact (((Complex.differentiableOn_dslope (hU.mem_nhds h0)).mpr hT).differentiableAt
      (hU.mem_nhds h0)).hasDerivAt
  have hgT : HasDerivAt (fun w => g (T w)) (g₁ * d) 0 :=
    (show HasDerivAt g g₁ (T 0) from hTa.symm ▸ hg).comp 0 h₁
  simpa only [Pi.pow_def, dslope_same, h₁.deriv, hTa, Pi.mul_def] using
    (hD.pow k).mul (hgT.mul h₂)

theorem LocalContourModel.coordinate_second_derivative {Z : Type*} [TopologicalSpace Z]
    {μ : ℕ} {a v : ℂ} {b : ℕ → Z → ℂ} {P : ℂ → Z → ℂ}
    {G : Set ℂ} {γ : ℝ → ℂ} (M : LocalContourModel μ a v (b 0) P G γ)
    (hG : IsOpen G) (ha : a ∈ G) (hb : ∀ z, b 0 z ≠ 0)
    (hs : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => b j z * (t - a) ^ (μ + j)) (P t z - P a z)) (z : Z) :
    HasDerivAt (deriv (fun t => saddleCoordinate μ a
      (fun z => leadingRoot μ v (b 0 z)) M.factor t z))
      (2 * leadingRoot μ v (b 0 z) * ((μ : ℂ)⁻¹ * (b 1 z / b 0 z))) a := by
  have hf := hasDerivAt_analytic_factor (q := fun t z => P t z - P a z)
    (h := M.factor) μ (hs z) (hb z) (M.factor_center z)
    (Filter.Eventually.mono (hG.mem_nhds ha) (fun t ht => M.phase_factorization t ht z))
  have hr : HasDerivAt (fun t => normalizedRoot μ (M.factor t z))
      ((μ : ℂ)⁻¹ * (b 1 z / b 0 z)) a := by
    simpa only [M.factor_center z, Function.comp_def] using
      (show HasDerivAt (normalizedRoot μ) ((μ : ℂ)⁻¹) (M.factor a z) from
        by rw [M.factor_center z]; exact hasDerivAt_normalizedRoot_one μ).comp a hf
  have hhol : DifferentiableOn ℂ (fun t => normalizedRoot μ (M.factor t z))
      (ball a M.inverseFamily.sourceRadius) :=
    (differentiableOn_normalizedRoot μ).comp
      ((M.factor_holomorphic z).mono M.inverseFamily.source_subset) (fun t ht => M.factor_slit t ht z)
  simpa only [saddleCoordinate, hr.deriv] using
    hasDerivAt_deriv_simple_factor (β := leadingRoot μ v (b 0 z)) isOpen_ball
      (mem_ball_self M.inverseFamily.sourceRadius_pos) hhol

theorem LocalContourModel.transformed_factor_first {Z : Type*} [TopologicalSpace Z]
    {μ : ℕ} {a v : ℂ} {b c : ℕ → Z → ℂ} {P q : ℂ → Z → ℂ}
    {G : Set ℂ} {γ : ℝ → ℂ} (M : LocalContourModel μ a v (b 0) P G γ)
    (hG : IsOpen G) (ha : a ∈ G) (hμ : μ ≠ 0) (hv : v ≠ 0) (hb : ∀ z, b 0 z ≠ 0)
    (hsP : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => b j z * (t - a) ^ (μ + j)) (P t z - P a z)) (k : ℕ)
    (hsq : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z)) (z : Z) :
    deriv (fun w => M.inverseFamily.amplitudeFactor k (phaseQuotient k a q) w z) 0 =
      (c 1 z - ((k : ℂ) + 2) * b 1 z * c 0 z / ((μ : ℂ) * b 0 z)) /
        leadingRoot μ v (b 0 z) ^ (k + 2) := by
  let β := fun z => leadingRoot μ v (b 0 z)
  have hβ : ∀ z, HasDerivAt (fun t => saddleCoordinate μ a β M.factor t z) (β z) a :=
    fun z => hasDerivAt_saddleCoordinate_center μ a β
      ((M.factor_holomorphic z).differentiableAt (hG.mem_nhds ha)) (M.factor_center z)
  have hβ0 : ∀ z, β z ≠ 0 := fun z => leadingRoot_ne_zero μ hv (b 0 z)
  have hz := saddleCoordinate_center μ a β M.factor
  have hT : HasDerivAt (fun w => M.inverseFamily.inverse w z) ((β z)⁻¹) 0 :=
    (M.inverseFamily.hasDerivAt_inverse_on_source M.inverseFamily.differentiableOn_sourceBall
      (mem_ball_self M.inverseFamily.targetRadius_pos) z).congr_deriv (by
        rw [M.inverseFamily.inverse_center hz z]
        exact congrArg Inv.inv (hβ z).deriv)
  have h₂ := M.inverseFamily.hasDerivAt_deriv_inverse_center hz hβ hβ0
    (M.coordinate_second_derivative hG ha hb hsP z)
  have hg : HasDerivAt (fun t => phaseQuotient k a q t z) (c 1 z) a := by
    have hd : DifferentiableAt ℂ (fun t => phaseQuotient k a q t z) a :=
      ((hasFPowerSeriesAt_of_shifted_expansion (hsq z)).has_fpower_series_iterate_dslope_fslope k).differentiableAt
    simpa only [deriv_phaseQuotient_center_of_expansion k (hsq z)] using hd.hasDerivAt
  have h := hasDerivAt_transformed_factor isOpen_ball (mem_ball_self M.inverseFamily.targetRadius_pos)
    (M.inverseFamily.differentiable_inverse z) (M.inverseFamily.inverse_center hz z) hT h₂ hg k
  have hraw := h.deriv
  change deriv (fun w => dslope (fun u => M.inverseFamily.inverse u z) 0 w ^ k *
    (phaseQuotient k a q (M.inverseFamily.inverse w z) z * deriv (fun u => M.inverseFamily.inverse u z) w)) 0 = _
  rw [hraw, phaseQuotient_center_of_expansion k (hsq z)]
  change _ = (c 1 z - ((k : ℂ) + 2) * b 1 z * c 0 z / ((μ : ℂ) * b 0 z)) / β z ^ (k + 2)
  have hμ0 : (μ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hμ
  change (k : ℂ) * (β z)⁻¹ ^ (k - 1) * (-(2 * β z * ((μ : ℂ)⁻¹ * (b 1 z / b 0 z))) / β z ^ 3 / 2) *
    (c 0 z * (β z)⁻¹) + (β z)⁻¹ ^ k *
    (c 1 z * (β z)⁻¹ * (β z)⁻¹ + c 0 z * (-(2 * β z * ((μ : ℂ)⁻¹ * (b 1 z / b 0 z))) / β z ^ 3)) = _
  cases k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul]
    field_simp [hβ0 z, hμ0, hb z]
    ring
  | succ k =>
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    simp only [inv_pow]
    field_simp [hβ0 z, hμ0, hb z]
    ring

end Neuschel
