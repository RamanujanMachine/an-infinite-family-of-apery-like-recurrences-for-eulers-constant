module

public import Neuschel.UniformLocal
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Analytic phase factors obtained by removing powers of the saddle variable. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

theorem norm_dslope_sub_le {f : ℂ → ℂ} {a c : ℂ} {r ε : ℝ} (hr : 0 < r)
    (hd : ∀ t ∈ ball a r, DifferentiableAt ℂ f t)
    (hb : ∀ t ∈ ball a r, ‖deriv f t - c‖ ≤ ε) {t : ℂ} (ht : t ∈ ball a r) :
    ‖dslope f a t - c‖ ≤ ε := by
  have hbound : ‖(f t - c * t) - (f a - c * a)‖ ≤ ε * ‖t - a‖ :=
    (convex_ball a r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => ((hd u hu).hasDerivAt.sub ((hasDerivAt_id u).const_mul c)).hasDerivWithinAt)
      (fun u hu => by simpa using hb u hu) (mem_ball_self hr) ht
  by_cases hne : t ≠ a
  · rw [dslope_of_ne f hne, slope_def_field, div_sub' (sub_ne_zero.mpr hne), norm_div,
      div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))]
    convert hbound using 2; ring
  · simpa [not_ne_iff.mp hne] using hb a (mem_ball_self hr)

variable {Z : Type*} [TopologicalSpace Z]

/-- Removing one zero preserves joint continuity, including at the saddle. -/
theorem continuousAt_dslope_family_center {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) (z : Z) :
    ContinuousAt (fun w : ℂ × Z => dslope (fun t => p t w.2) a w.1) (a, z) := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp
    (Metric.tendsto_nhds.mp
      ((continuousOn_deriv_family hG hp hd).continuousAt (x := (a, z))
        ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).tendsto (ε / 2) (half_pos hε))
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (hG.mem_nhds ha))
  filter_upwards [mem_nhds_prod_iff.mpr ⟨ball a r, ball_mem_nhds a hr, V, hV, Subset.rfl⟩]
    with w hw
  simpa only [dslope_same, dist_eq_norm] using
    (norm_dslope_sub_le hr
      (fun t ht => (hd w.2).differentiableAt (hG.mem_nhds (hrU ht).2))
      (fun t ht => (show ‖deriv (fun t => p t w.2) t - deriv (fun t => p t z) a‖ < ε / 2
        by simpa only [dist_eq_norm, Set.mem_ofPred_eq] using
          hUV (show (t, w.2) ∈ U ×ˢ V from ⟨(hrU ht).1, hw.2⟩)).le) hw.1).trans_lt
      (half_lt_self hε)

theorem continuousOn_dslope_family {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) :
    ContinuousOn (fun w : ℂ × Z => dslope (fun t => p t w.2) a w.1) (G ×ˢ univ) := by
  rintro ⟨t, z⟩ ⟨ht, _⟩
  by_cases he : t = a
  · exact he ▸ (continuousAt_dslope_family_center hG ha hp hd z).continuousWithinAt
  · have hcenter : Continuous (fun z => p a z) :=
      hp.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
    have hquot : ContinuousAt (fun w : ℂ × Z => (p w.1 w.2 - p a w.2) / (w.1 - a)) (t, z) :=
      ((hp.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ht, mem_univ z⟩)).sub
        (hcenter.continuousAt.comp continuousAt_snd)).div
        (continuousAt_fst.sub continuousAt_const) (sub_ne_zero.mpr he)
    apply ContinuousAt.continuousWithinAt
      (hquot.congr_of_eventuallyEq ?_)
    filter_upwards [continuousAt_fst.tendsto.eventually (isOpen_ne.mem_nhds he)] with w hw
    rw [dslope_of_ne _ hw, slope_def_field]

/-- Canonical analytic quotient after removing `n` powers of `t-a`. -/
@[expose] noncomputable def phaseQuotient (n : ℕ) (a : ℂ) (p : ℂ → Z → ℂ) (t : ℂ) (z : Z) : ℂ :=
  (Function.swap dslope a)^[n] (fun u => p u z) t

theorem phaseQuotient_regular (n : ℕ) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) :
    ContinuousOn (Function.uncurry (phaseQuotient n a p)) (G ×ˢ univ) ∧
      ∀ z, DifferentiableOn ℂ (fun t => phaseQuotient n a p t z) G := by
  induction n with
  | zero => exact ⟨hp, hd⟩
  | succ n ih =>
    simpa only [Function.uncurry_def, phaseQuotient, Function.iterate_succ_apply', Function.swap] using
      (show ContinuousOn (fun w : ℂ × Z => dslope (fun t => phaseQuotient n a p t w.2) a w.1)
          (G ×ˢ univ) ∧ ∀ z, DifferentiableOn ℂ
            (fun t => dslope (fun u => phaseQuotient n a p u z) a t) G from
        ⟨continuousOn_dslope_family hG ha ih.1 ih.2,
          fun z => (Complex.differentiableOn_dslope (hG.mem_nhds ha)).mpr (ih.2 z)⟩)

omit [TopologicalSpace Z] in
theorem phaseQuotient_center_eq_coeff (n : ℕ) {a : ℂ} {p : ℂ → Z → ℂ} {z : Z}
    {s : FormalMultilinearSeries ℂ ℂ ℂ} (hs : HasFPowerSeriesAt (fun t => p t z) s a) :
    phaseQuotient n a p a z = s.coeff n := by
  have hc := (hs.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1
  change (FormalMultilinearSeries.fslope^[n] s).coeff 0 = phaseQuotient n a p a z at hc
  simpa only [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] using hc.symm

omit [TopologicalSpace Z] in
theorem eq_pow_mul_phaseQuotient (μ : ℕ) {a : ℂ} {p : ℂ → Z → ℂ} {z : Z}
    {s : FormalMultilinearSeries ℂ ℂ ℂ} (hs : HasFPowerSeriesAt (fun t => p t z) s a)
    (hzero : ∀ n < μ, s.coeff n = 0) (t : ℂ) :
    p t z = (t - a) ^ μ * phaseQuotient μ a p t z := by
  simpa only [smul_eq_mul, phaseQuotient] using
    (pow_sub_smul_iterate_dslope_of_zero μ
      (fun n hn => (phaseQuotient_center_eq_coeff n hs).trans (hzero n hn)) t).symm

/-- Taylor coefficients vary continuously with the parameter; no coefficient
continuity or common radius of convergence is assumed. -/
theorem continuous_coeff_family (n : ℕ) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    {s : Z → FormalMultilinearSeries ℂ ℂ ℂ}
    (hs : ∀ z, HasFPowerSeriesAt (fun t => p t z) (s z) a) :
    Continuous (fun z => (s z).coeff n) :=
  (((phaseQuotient_regular n hG ha hp hd).1).comp_continuous
    (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)).congr
      (fun z => phaseQuotient_center_eq_coeff n (hs z))

/-- Remove the vanishing Taylor terms and normalize by the first nonzero
coefficient. Joint regularity of the factor follows from that of the phase. -/
theorem exists_normalized_analytic_factor (μ : ℕ) {G : Set ℂ} (hG : IsOpen G)
    {a : ℂ} (ha : a ∈ G) {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    {s : Z → FormalMultilinearSeries ℂ ℂ ℂ}
    (hs : ∀ z, HasFPowerSeriesAt (fun t => p t z) (s z) a)
    (hzero : ∀ z, ∀ n < μ, (s z).coeff n = 0) (hne : ∀ z, (s z).coeff μ ≠ 0) :
    ∃ h : ℂ → Z → ℂ, ContinuousOn (Function.uncurry h) (G ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun t => h t z) G) ∧ (∀ z, h a z = 1) ∧
      ∀ t ∈ G, ∀ z, p t z = (s z).coeff μ * (t - a) ^ μ * h t z := by
  have hq := phaseQuotient_regular μ hG ha hp hd
  refine ⟨fun t z => phaseQuotient μ a p t z / (s z).coeff μ,
    hq.1.div ((continuous_coeff_family μ hG ha hp hd hs).comp continuous_snd).continuousOn
      (fun w _ => hne w.2),
    fun z => (hq.2 z).div_const _,
    fun z => (congrArg (fun u : ℂ => u / (s z).coeff μ)
      (phaseQuotient_center_eq_coeff μ (hs z))).trans (div_self (hne z)), ?_⟩
  intro t _ z
  rw [eq_pow_mul_phaseQuotient μ (hs z) (hzero z) t]
  field_simp [hne z]

/-- The normalized phase factor required by the saddle-coordinate construction,
derived from a Taylor expansion of `p(t,z)-p(a,z)`. -/
theorem exists_normalized_phase_factor (μ : ℕ) {G : Set ℂ} (hG : IsOpen G)
    {a : ℂ} (ha : a ∈ G) {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    {s : Z → FormalMultilinearSeries ℂ ℂ ℂ}
    (hs : ∀ z, HasFPowerSeriesAt (fun t => p t z - p a z) (s z) a)
    (hzero : ∀ z, ∀ n < μ, (s z).coeff n = 0) (hne : ∀ z, (s z).coeff μ ≠ 0) :
    Continuous (fun z => (s z).coeff μ) ∧
    ∃ h : ℂ → Z → ℂ, ContinuousOn (Function.uncurry h) (G ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun t => h t z) G) ∧ (∀ z, h a z = 1) ∧
      ∀ t ∈ G, ∀ z, p t z - p a z = (s z).coeff μ * (t - a) ^ μ * h t z := by
  have hcenter : Continuous (fun z => p a z) :=
    hp.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
  have hf : ContinuousOn (Function.uncurry (fun t z => p t z - p a z)) (G ×ˢ univ) :=
    hp.sub (hcenter.comp continuous_snd).continuousOn
  exact ⟨continuous_coeff_family μ hG ha hf (fun z => (hd z).sub_const _) hs,
    exists_normalized_analytic_factor μ hG ha hf (fun z => (hd z).sub_const _) hs hzero hne⟩

end Neuschel
