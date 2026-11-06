module

public import Neuschel.ContourCutoff

/-! A uniform local contour model derived from the original phase hypotheses. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

variable {Z : Type*} [TopologicalSpace Z]

/-- The local change of variable, a common contour cutoff, the correct branch,
and a uniform positive phase gap at the cutoff. -/
structure LocalContourModel (μ : ℕ) (a v : ℂ) (b : Z → ℂ) (P : ℂ → Z → ℂ)
    (G : Set ℂ) (γ : ℝ → ℂ) where
  factor : ℂ → Z → ℂ
  factor_continuous : ContinuousOn (Function.uncurry factor) (G ×ˢ univ)
  factor_holomorphic : ∀ z, DifferentiableOn ℂ (fun t => factor t z) G
  factor_center : ∀ z, factor a z = 1
  phase_factorization : ∀ t ∈ G, ∀ z, P t z - P a z = b z * (t - a) ^ μ * factor t z
  inverseFamily : LocalInverseFamily (saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) factor) a G
  factor_slit : ∀ t ∈ ball a inverseFamily.sourceRadius, ∀ z, factor t z ∈ Complex.slitPlane
  cutoff : ℝ
  cutoff_mem : cutoff ∈ Ioo (0 : ℝ) 1
  contour_in_source : ∀ s ∈ Icc (0 : ℝ) cutoff, ∀ z, γ s ∈ inverseFamily.source z
  image_small : ∀ s ∈ Icc (0 : ℝ) cutoff, ∀ z,
    saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) factor (γ s) z ∈
      ball 0 (inverseFamily.targetRadius / 2)
  principal_root : ∀ s ∈ Ioc (0 : ℝ) cutoff, ∀ z,
    saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) factor (γ s) z =
      normalizedRoot μ (P (γ s) z - P a z)
  phase_inverse : ∀ w ∈ ball 0 inverseFamily.targetRadius, ∀ z,
    P (inverseFamily.inverse w z) z - P a z = w ^ μ
  endpoint_phase_continuous : Continuous (fun z => P (γ cutoff) z - P a z)
  endpoint_gap : ℝ
  endpoint_gap_pos : 0 < endpoint_gap
  endpoint_gap_le : ∀ z, endpoint_gap ≤ (P (γ cutoff) z - P a z).re

theorem exists_localContourModel_below [CompactSpace Z] [Nonempty Z] {G : Set ℂ}
    (hG : IsOpen G) {a : ℂ} (ha : a ∈ G) {μ : ℕ} (hμ : μ ≠ 0)
    {P : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => P t z) G) {b : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun n => b n z * (t - a) ^ (μ + n)) (P t z - P a z)) (hb0 : ∀ z, b 0 z ≠ 0)
    {γ : ℝ → ℂ} {v : ℂ} (hγ : HasDerivWithinAt γ v (Ici 0) 0)
    (hγ0 : γ 0 = a) (hv : v ≠ 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (P (γ s) z - P a z).re)
    {L : ℝ} (hL : 0 < L) :
    ∃ M : LocalContourModel μ a v (b 0) P G γ, M.cutoff < L := by
  obtain ⟨hb, h, hh, hdh, hc, hf⟩ := exists_phase_factor_from_expansion μ hG ha hp hd hs hb0
  have hposNear : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z, 0 ≤ (P (γ s) z - P a z).re := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with s hs0 hs1 z
    exact (hpos s ⟨hs0, hs1⟩ z).le
  have hsector : ∀ z, 0 ≤ (b 0 z * v ^ μ).re := fun z =>
    phase_sector_of_contour (p := fun t => P t z) (h := fun t => h t z) μ hγ hγ0
      ((hh.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).comp
        (continuousAt_id.prodMk continuousAt_const)) (hc z)
      (((tendsto_contour_endpoint hγ hγ0).eventually (hG.mem_nhds ha)).mono
        (fun s hs => hf (γ s) hs z)) (hposNear.mono (fun _ hs => hs z))
  have hβ := continuous_leadingRoot μ v hb (fun z => mem_slitPlane_of_re_nonneg (hsector z)
    (mul_ne_zero (hb0 z) (pow_ne_zero μ hv)))
  obtain ⟨e, hslit⟩ := exists_saddleCoordinate_inverse hG ha μ hβ
    (fun z => leadingRoot_ne_zero μ hv (b 0 z)) hh hdh hc
  obtain ⟨δ, hδ, hsmall, hbranch⟩ := e.exists_common_contour_cutoff
    (continuousOn_saddleCoordinate μ a hβ (hh.mono (Set.prod_mono e.source_subset Subset.rfl)) hslit)
    (saddleCoordinate_center μ a _ h) (tendsto_contour_endpoint hγ hγ0) hγ0
    ((eventually_principal_phase_root hμ hG ha hb hb0 hγ hγ0 hv hsector hh hc hf).and
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds hL)))
  have hα : Continuous (fun z => P (γ δ) z - P a z) :=
    (hp.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨e.source_subset (hsmall δ (right_mem_Icc.mpr hδ.1.le) z).1.1, mem_univ z⟩)).sub
      (hp.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩))
  obtain ⟨η, hη, hgap⟩ := exists_positive_re_gap hα (hpos δ hδ)
  have hpower : ∀ t ∈ ball a e.sourceRadius, ∀ z,
      saddleCoordinate μ a (fun z => leadingRoot μ v (b 0 z)) h t z ^ μ = P t z - P a z :=
    fun t ht z => by
      simpa only [leadingRoot_pow hμ hv (hb0 z), hf t (e.source_subset ht) z] using
        saddleCoordinate_pow hμ a (fun z => leadingRoot μ v (b 0 z)) h
          (Complex.slitPlane_ne_zero (hslit t ht z))
  exact ⟨{
    factor := h
    factor_continuous := hh
    factor_holomorphic := hdh
    factor_center := hc
    phase_factorization := hf
    inverseFamily := e
    factor_slit := hslit
    cutoff := δ
    cutoff_mem := hδ
    contour_in_source := fun s hs z => (hsmall s hs z).1
    image_small := fun s hs z => (hsmall s hs z).2
    principal_root := fun s hs z => (hbranch s hs).1 z
    phase_inverse := fun w hw z =>
      (hpower (e.inverse w z) (e.inverse_mem w hw z) z).symm.trans
        (congrArg (fun u : ℂ => u ^ μ) (e.right_inv w hw z))
    endpoint_phase_continuous := hα
    endpoint_gap := η
    endpoint_gap_pos := hη
    endpoint_gap_le := hgap
  }, (hbranch δ (right_mem_Ioc.mpr hδ.1)).2⟩

theorem exists_localContourModel [CompactSpace Z] [Nonempty Z] {G : Set ℂ}
    (hG : IsOpen G) {a : ℂ} (ha : a ∈ G) {μ : ℕ} (hμ : μ ≠ 0)
    {P : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => P t z) G) {b : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun n => b n z * (t - a) ^ (μ + n)) (P t z - P a z)) (hb0 : ∀ z, b 0 z ≠ 0)
    {γ : ℝ → ℂ} {v : ℂ} (hγ : HasDerivWithinAt γ v (Ici 0) 0)
    (hγ0 : γ 0 = a) (hv : v ≠ 0)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (P (γ s) z - P a z).re) :
    Nonempty (LocalContourModel μ a v (b 0) P G γ) := by
  obtain ⟨M, _⟩ := exists_localContourModel_below hG ha hμ hp hd hs hb0 hγ hγ0 hv hpos zero_lt_one
  exact ⟨M⟩

end Neuschel
