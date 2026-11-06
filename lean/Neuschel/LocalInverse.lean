module

public import Neuschel.UniformLocal
public import Mathlib.Analysis.Complex.Conformal

/-!
# Uniform local inverses

The common inverse domain and continuity assertions of Neuschel's Lemma 2.2.
The proof uses quantitative inverse estimates instead of Rouché's theorem.
-/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology NNReal

variable {Z : Type*} [TopologicalSpace Z]

/-- A holomorphic inverse family on one target disk, with a common source disk
inside the original domain. -/
structure LocalInverseFamily (p : ℂ → Z → ℂ) (a : ℂ) (G : Set ℂ) where
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  targetRadius : ℝ
  targetRadius_pos : 0 < targetRadius
  source_subset : ball a sourceRadius ⊆ G
  deriv_ne_zero : ∀ t ∈ ball a sourceRadius, ∀ z, deriv (fun u => p u z) t ≠ 0
  inverse : ℂ → Z → ℂ
  inverse_mem : ∀ w ∈ ball 0 targetRadius, ∀ z, inverse w z ∈ ball a sourceRadius
  right_inv : ∀ w ∈ ball 0 targetRadius, ∀ z, p (inverse w z) z = w
  left_inv : ∀ z, ∀ t ∈ ball a sourceRadius, p t z ∈ ball 0 targetRadius →
    inverse (p t z) z = t
  continuous_inverse : ContinuousOn (Function.uncurry inverse) (ball 0 targetRadius ×ˢ univ)
  differentiable_inverse : ∀ z, DifferentiableOn ℂ (fun w => inverse w z) (ball 0 targetRadius)
  continuous_deriv_inverse : ContinuousOn
    (fun w : ℂ × Z => deriv (fun u => inverse u w.2) w.1) (ball 0 targetRadius ×ˢ univ)

/-- The uniform inverse-family assertions in Neuschel's Lemma 2.2, under precisely
its local analytic assumptions (with an arbitrary compact parameter type). -/
theorem exists_localInverseFamily {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hz : ∀ z, p a z = 0) (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) :
    Nonempty (LocalInverseFamily p a G) := by
  obtain ⟨s, hs, hsG, hsD⟩ := exists_uniform_deriv_ne_zero hG ha hp hd hne
  obtain ⟨r, hr, δ, hδ, hU, hA, hI, hS⟩ := exists_uniform_image_disk
    (hG.inter isOpen_ball) ⟨ha, mem_ball_self hs⟩
    (hp.mono (Set.prod_mono inter_subset_left Subset.rfl))
    (fun z => (hd z).mono inter_subset_left) hz hne
  let q : ℂ → Z → ℂ := fun w z => Function.invFunOn (fun t => p t z) (ball a r) w
  have hq : ∀ w ∈ ball 0 δ, ∀ z, q w z ∈ ball a r :=
    fun w hw z => Function.invFunOn_mem (hS z (ball_subset_closedBall hw))
  have hright : ∀ w ∈ ball 0 δ, ∀ z, p (q w z) z = w :=
    fun w hw z => Function.invFunOn_eq (hS z (ball_subset_closedBall hw))
  have hdc : Continuous (fun z => deriv (fun t => p t z) a) :=
    (continuousOn_deriv_family hG hp hd).comp_continuous
      (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
  have hN : ContinuousOn
      (fun w : ℂ × Z => p w.1 w.2 / deriv (fun t => p t w.2) a) (ball a r ×ˢ univ) :=
    (hp.mono (Set.prod_mono (fun t ht => (hU ht).1) Subset.rfl)).div
      (hdc.comp continuous_snd).continuousOn (fun w _ => hne w.2)
  have hv : ContinuousOn
      (fun w : ℂ × Z => w.1 / deriv (fun t => p t w.2) a) (ball 0 δ ×ˢ univ) :=
    (continuous_fst.div (hdc.comp continuous_snd) (fun w => hne w.2)).continuousOn
  have hcq : ContinuousOn (Function.uncurry q) (ball 0 δ ×ˢ univ) :=
    continuousOn_inverse_family (L := 2)
      (p := fun t z => p t z / deriv (fun u => p u z) a)
      (v := fun w z => w / deriv (fun u => p u z) a) hN hv
      (fun z _ hx _ hy => dist_le_of_approximates_id_half (hA z) hx hy) hq
      (fun w hw z => congrArg (fun v => v / deriv (fun t => p t z) a) (hright w hw z))
  suffices hqd : ∀ z, DifferentiableOn ℂ (fun w => q w z) (ball 0 δ) by
    exact ⟨{
      sourceRadius := r
      sourceRadius_pos := hr
      targetRadius := δ
      targetRadius_pos := hδ
      source_subset := fun t ht => (hU ht).1
      deriv_ne_zero := fun t ht z => hsD t (hU ht).2 z
      inverse := q
      inverse_mem := hq
      right_inv := hright
      left_inv := fun z t ht _ => (hI z).leftInvOn_invFunOn ht
      continuous_inverse := hcq
      differentiable_inverse := hqd
      continuous_deriv_inverse := continuousOn_deriv_family isOpen_ball hcq hqd
    }⟩
  intro z w hw
  have hqcw : ContinuousAt (fun w => q w z) w :=
    (hcq.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hw, mem_univ z⟩)).comp
      (continuousAt_id.prodMk continuousAt_const)
  exact (HasDerivAt.of_local_left_inverse hqcw
    ((hd z).differentiableAt (hG.mem_nhds (hU (hq w hw z)).1)).hasDerivAt
    (hsD (q w z) (hU (hq w hw z)).2 z)
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hw) (fun u hu => hright u hu z)))
    |>.differentiableAt.differentiableWithinAt

namespace LocalInverseFamily

variable {G : Set ℂ} {a : ℂ} {p : ℂ → Z → ℂ} (e : LocalInverseFamily p a G)

/-- The open source domain mapped bijectively to the common target disk. -/
@[expose] def source (z : Z) : Set ℂ :=
  ball a e.sourceRadius ∩ (fun t => p t z) ⁻¹' ball 0 e.targetRadius

theorem inverse_mem_source {w : ℂ} (hw : w ∈ ball 0 e.targetRadius) (z : Z) :
    e.inverse w z ∈ e.source z :=
  ⟨e.inverse_mem w hw z,
    show p (e.inverse w z) z ∈ ball 0 e.targetRadius from (e.right_inv w hw z).symm ▸ hw⟩

theorem source_eq_image_inverse (z : Z) :
    e.source z = (fun w => e.inverse w z) '' ball 0 e.targetRadius :=
  Set.Subset.antisymm
    (fun t ht => ⟨p t z, ht.2, e.left_inv z t ht.1 ht.2⟩)
    (image_subset_iff.mpr (fun _ hw => e.inverse_mem_source hw z))

theorem isOpen_source (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) (z : Z) :
    IsOpen (e.source z) :=
  ((hd z).mono e.source_subset).continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball

theorem isPreconnected_source (z : Z) : IsPreconnected (e.source z) := by
  rw [e.source_eq_image_inverse z]
  exact (convex_ball (0 : ℂ) e.targetRadius).isPreconnected.image _
    (e.differentiable_inverse z).continuousOn

theorem isConnected_source (z : Z) : IsConnected (e.source z) :=
  ⟨⟨e.inverse 0 z, e.inverse_mem_source (mem_ball_self e.targetRadius_pos) z⟩,
    e.isPreconnected_source z⟩

theorem center_mem_source (hz : ∀ z, p a z = 0) (z : Z) : a ∈ e.source z :=
  ⟨mem_ball_self e.sourceRadius_pos,
    show p a z ∈ ball 0 e.targetRadius from (hz z).symm ▸ mem_ball_self e.targetRadius_pos⟩

theorem bijOn_source (z : Z) : BijOn (fun t => p t z) (e.source z) (ball 0 e.targetRadius) :=
  ⟨(fun _ ht => ht.2),
    (fun x hx y hy hxy => (e.left_inv z x hx.1 hx.2).symm.trans
      ((congrArg (fun w => e.inverse w z) hxy).trans (e.left_inv z y hy.1 hy.2))),
    (fun w hw => ⟨e.inverse w z, e.inverse_mem_source hw z, e.right_inv w hw z⟩)⟩

theorem conformalAt_source (hG : IsOpen G)
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) (z : Z) {t : ℂ} (ht : t ∈ e.source z) :
    ConformalAt (fun u => p u z) t :=
  ((hd z).differentiableAt (hG.mem_nhds (e.source_subset ht.1))).conformalAt
    (e.deriv_ne_zero t ht.1 z)

theorem hasDerivAt_inverse (hG : IsOpen G)
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    {w : ℂ} (hw : w ∈ ball 0 e.targetRadius) (z : Z) :
    HasDerivAt (fun u => e.inverse u z) (deriv (fun t => p t z) (e.inverse w z))⁻¹ w :=
  HasDerivAt.of_local_left_inverse
    ((e.differentiable_inverse z).differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
    ((hd z).differentiableAt (hG.mem_nhds (e.source_subset (e.inverse_mem w hw z)))).hasDerivAt
    (e.deriv_ne_zero (e.inverse w z) (e.inverse_mem w hw z) z)
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hw) (fun u hu => e.right_inv u hu z))

theorem conformalAt_inverse (hG : IsOpen G)
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    {w : ℂ} (hw : w ∈ ball 0 e.targetRadius) (z : Z) :
    ConformalAt (fun u => e.inverse u z) w := by
  have h := e.hasDerivAt_inverse hG hd hw z
  exact h.differentiableAt.conformalAt (by
    simpa only [h.deriv] using inv_ne_zero (e.deriv_ne_zero (e.inverse w z) (e.inverse_mem w hw z) z))

/-- One neighborhood of the center lies in every inverse source domain. -/
theorem exists_common_source_disk [CompactSpace Z]
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ)) (hz : ∀ z, p a z = 0) :
    ∃ ε > 0, ball a ε ⊆ ⋂ z, e.source z := by
  obtain ⟨ε, hε, hU, hMap⟩ := exists_uniform_mapsTo_nhds isOpen_ball
    (mem_ball_self e.sourceRadius_pos)
    (hp.mono (Set.prod_mono e.source_subset Subset.rfl)) isOpen_ball
    (fun z => (show p a z ∈ ball 0 e.targetRadius from
      (hz z).symm ▸ mem_ball_self e.targetRadius_pos))
  exact ⟨ε, hε, fun t ht => mem_iInter.mpr (fun z => ⟨hU ht, hMap z ht⟩)⟩

end LocalInverseFamily

/-- **Neuschel, Lemma 2.2.** Uniform holomorphic inverses on a common disk,
joint continuity of inverses and their derivatives, open connected source
neighborhoods, a common source disk, and a common image neighborhood of zero.

The inverse and derivative assertions are fields of `LocalInverseFamily`.
The bijection assertions, together with holomorphy and nonzero derivatives,
give the conformal maps in the published statement.
-/
theorem neuschel_lemma_2_2 {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hz : ∀ z, p a z = 0) (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) :
    ∃ e : LocalInverseFamily p a G,
      (∀ z, IsOpen (e.source z) ∧ IsConnected (e.source z) ∧ a ∈ e.source z ∧
        BijOn (fun t => p t z) (e.source z) (ball 0 e.targetRadius) ∧
        ∀ t ∈ e.source z, ConformalAt (fun u => p u z) t) ∧
      ∃ ε > 0, ball a ε ⊆ ⋂ z, e.source z ∧
        (0 : ℂ) ∈ interior (⋂ z, (fun t => p t z) '' ball a ε) := by
  obtain ⟨e⟩ := exists_localInverseFamily hG ha hp hd hz hne
  obtain ⟨ε, hε, hsource⟩ := e.exists_common_source_disk hp hz
  exact ⟨e, (fun z => ⟨e.isOpen_source hd z, e.isConnected_source z,
    e.center_mem_source hz z, e.bijOn_source z, fun _ ht => e.conformalAt_source hG hd z ht⟩),
    ε, hε, hsource,
    zero_mem_interior_iInter_image_ball hG ha hp hd hz hne hε⟩

end Neuschel
