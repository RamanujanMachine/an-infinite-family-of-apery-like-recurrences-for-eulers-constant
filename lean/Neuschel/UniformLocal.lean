module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform local analysis for Neuschel's Laplace theorem

The target is the parameter-uniform local theory in Section 2 of
Thorsten Neuschel, *A uniform version of Laplace's method for contour integrals*,
Analysis 32 (2012), 121–135, DOI: 10.1524/anly.2012.1147.

No result in this file is imported from the author's application or assumed as an axiom.
-/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology NNReal

variable {Z : Type*} [TopologicalSpace Z]

/-- A jointly continuous family converges locally uniformly when its parameter tends
to a fixed value. The complex variable ranges over an open domain. -/
theorem tendstoLocallyUniformlyOn_family {G : Set ℂ} (hG : IsOpen G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ)) (z : Z) :
    TendstoLocallyUniformlyOn (fun z t => p t z) (fun t => p t z) (𝓝 z) G := by
  refine hG.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr ?_
  intro x hx
  have hpc : ContinuousAt (Function.uncurry p) (x, z) :=
    hp.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z⟩)
  exact ((hpc.tendsto.comp (tendsto_snd.prodMk_nhds tendsto_const_nhds)).prodMk_nhds
    (hpc.tendsto.comp (tendsto_snd.prodMk_nhds tendsto_fst))).mono_right
      (nhds_le_uniformity _)

/-- Joint continuity of a holomorphic family is preserved by differentiation in its
complex variable. This is the assertion used in Lemma 2.2(i). -/
theorem continuousOn_deriv_family {G : Set ℂ} (hG : IsOpen G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) :
    ContinuousOn (fun w : ℂ × Z => deriv (fun t => p t w.2) w.1) (G ×ˢ univ) := by
  intro w hw
  apply ContinuousAt.continuousWithinAt
  have hloc := (tendstoLocallyUniformlyOn_family hG hp w.2).deriv
    (Filter.Eventually.of_forall hd) hG
  have hlim : ContinuousAt (deriv (fun t => p t w.2)) w.1 :=
    ((hd w.2).deriv hG).continuousOn.continuousAt (hG.mem_nhds hw.1)
  exact (hlim.tendsto.comp continuousAt_fst.tendsto).congr_uniformity
    ((hG.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hloc w.1 hw.1).comp
      (continuousAt_snd.tendsto.prodMk continuousAt_fst.tendsto))

/-- Compactness gives one disk on which all normalized derivatives are close to one.
The derivative at the center is allowed to vary with the parameter. -/
theorem exists_uniform_deriv_near {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ t ∈ ball a r, ∀ z,
      ‖(deriv (fun u => p u z) t - deriv (fun u => p u z) a) /
        deriv (fun u => p u z) a‖ < ε := by
  have hDp := continuousOn_deriv_family hG hp hd
  have hdc : Continuous (fun z => deriv (fun t => p t z) a) :=
    hDp.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
  have hn : ContinuousOn (fun w : ℂ × Z =>
      (deriv (fun t => p t w.2) w.1 - deriv (fun t => p t w.2) a) /
        deriv (fun t => p t w.2) a) (G ×ˢ univ) :=
    (hDp.sub (hdc.comp continuous_snd).continuousOn).div
      (hdc.comp continuous_snd).continuousOn (fun w _ => hne w.2)
  have hnear : ∀ᶠ t in 𝓝 a, ∀ z ∈ (univ : Set Z),
      ‖(deriv (fun u => p u z) t - deriv (fun u => p u z) a) /
        deriv (fun u => p u z) a‖ < ε :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun z _ =>
      (hn.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).norm.tendsto.eventually
        (gt_mem_nhds (by simpa only [sub_self, zero_div, norm_zero] using hε)))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hnear.and (hG.mem_nhds ha))
  exact ⟨r, hr, fun t ht => (hb t ht).2, fun t ht z => (hb t ht).1 z (mem_univ z)⟩

/-- A derivative uniformly close to one gives a quantitative approximation to the
identity on a convex disk. -/
theorem approximates_id_of_deriv_near {f : ℂ → ℂ} {a : ℂ} {r : ℝ} {c : ℝ≥0}
    (hd : ∀ t ∈ ball a r, DifferentiableAt ℂ f t)
    (hb : ∀ t ∈ ball a r, ‖deriv f t - 1‖ ≤ c) :
    ApproximatesLinearOn f (ContinuousLinearMap.id ℂ ℂ) (ball a r) c := by
  rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith]
  refine (convex_ball a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => ((hd t ht).hasDerivAt.sub (hasDerivAt_id t)).hasDerivWithinAt) ?_
  exact fun t ht => NNReal.coe_le_coe.mp (hb t ht)

/-- A compact holomorphic family with nonzero derivative at a fixed point admits a
uniform quantitative inverse-function neighborhood after normalizing each derivative. -/
theorem exists_uniform_approximates {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) {c : ℝ≥0} (hc : 0 < c) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ z,
      ApproximatesLinearOn (fun t => p t z / deriv (fun u => p u z) a)
        (ContinuousLinearMap.id ℂ ℂ) (ball a r) c := by
  obtain ⟨r, hr, hG', hb⟩ := exists_uniform_deriv_near hG ha hp hd hne
    (show (0 : ℝ) < c from hc)
  refine ⟨r, hr, hG', fun z => approximates_id_of_deriv_near
    (fun t ht => ((hd z).differentiableAt (hG.mem_nhds (hG' ht))).div_const _) ?_⟩
  simpa only [deriv_div_const, sub_div, div_self (hne z)] using fun t ht => (hb t ht z).le

/-- The functions of a compact holomorphic family are all injective on one common
disk around a point where their derivatives are nonzero. -/
theorem exists_uniform_injOn {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ z, InjOn (fun t => p t z) (ball a r) := by
  obtain ⟨r, hr, hG', hb⟩ := exists_uniform_approximates hG ha hp hd hne
    (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  exact ⟨r, hr, hG', fun z x hx y hy hxy =>
    (hb z).injOn (f' := ContinuousLinearEquiv.refl ℂ ℂ) (Or.inr (by norm_num)) hx hy
      (congrArg (fun v => v / deriv (fun u => p u z) a) hxy)⟩

/-- **Neuschel, Lemma 2.1.** A common simple zero is uniformly isolated over a
compact parameter space. -/
theorem exists_uniform_isolated_zero {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hz : ∀ z, p a z = 0) (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ t ∈ ball a r, t ≠ a → ∀ z, p t z ≠ 0 := by
  obtain ⟨r, hr, hG', hi⟩ := exists_uniform_injOn hG ha hp hd hne
  exact ⟨r, hr, hG', fun t ht hta z htz =>
    hta (hi z ht (mem_ball_self hr) (htz.trans (hz z).symm))⟩

/-- An explicit image estimate for a map whose nonlinear part has Lipschitz
constant at most one half. -/
theorem closedBall_subset_image_of_approximates_id {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id ℂ ℂ) (ball a r) (1 / 2)) :
    closedBall (f a) (r / 4) ⊆ f '' ball a r := by
  have hsmall : closedBall a (r / 2) ⊆ ball a r :=
    closedBall_subset_ball (half_lt_self hr)
  have himage := hf.closedBall_subset_target (f' := ContinuousLinearEquiv.refl ℂ ℂ)
    (Or.inr (by norm_num)) isOpen_ball (show 0 ≤ r / 2 from (half_pos hr).le) hsmall
  convert himage using 1
  all_goals norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- There is a common disk in the images of a sufficiently small common
injectivity disk. This is the uniform image-radius assertion in Lemma 2.2. -/
theorem exists_uniform_image_disk {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hz : ∀ z, p a z = 0) (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ball a r ⊆ G ∧
      (∀ z, ApproximatesLinearOn (fun t => p t z / deriv (fun u => p u z) a)
        (ContinuousLinearMap.id ℂ ℂ) (ball a r) (1 / 2)) ∧
      (∀ z, InjOn (fun t => p t z) (ball a r)) ∧
      (∀ z, closedBall 0 δ ⊆ (fun t => p t z) '' ball a r) := by
  obtain ⟨r, hr, hG', hb⟩ := exists_uniform_approximates hG ha hp hd hne
    (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  have hdc : Continuous (fun z => deriv (fun t => p t z) a) :=
    (continuousOn_deriv_family hG hp hd).comp_continuous
      (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
  obtain ⟨m, hm, hm'⟩ := isCompact_univ.exists_forall_le' hdc.norm.continuousOn
    (fun z _ => norm_pos_iff.mpr (hne z))
  refine ⟨r, hr, m * r / 4, div_pos (mul_pos hm hr) (by norm_num), hG', hb,
    fun z x hx y hy hxy => (hb z).injOn (f' := ContinuousLinearEquiv.refl ℂ ℂ)
      (Or.inr (by norm_num)) hx hy
        (congrArg (fun v => v / deriv (fun u => p u z) a) hxy), ?_⟩
  intro z w hw
  have hw' : ‖w‖ ≤ m * r / 4 := by simpa only [mem_closedBall, dist_zero_right] using hw
  have hscale : ‖w‖ ≤ (r / 4) * ‖deriv (fun u => p u z) a‖ := by
    nlinarith [hm' z (mem_univ z)]
  have hwN : w / deriv (fun u => p u z) a ∈
      closedBall (p a z / deriv (fun u => p u z) a) (r / 4) := by
    simpa only [hz z, zero_div, mem_closedBall, dist_zero_right, norm_div] using
      (div_le_iff₀ (norm_pos_iff.mpr (hne z))).mpr hscale
  obtain ⟨t, ht, htw⟩ := closedBall_subset_image_of_approximates_id hr (hb z) hwN
  exact ⟨t, ht, (div_left_inj' (hne z)).mp htw⟩

/-- A quantitative inverse estimate turns joint continuity of a family and its
right-hand side into joint continuity of any corresponding family of inverse values. -/
theorem continuousOn_inverse_family {U V : Set ℂ} {p q v : ℂ → Z → ℂ} {L : ℝ≥0}
    (hp : ContinuousOn (Function.uncurry p) (U ×ˢ univ))
    (hv : ContinuousOn (Function.uncurry v) (V ×ˢ univ))
    (hbound : ∀ z, ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ L * dist (p x z) (p y z))
    (hq : ∀ w ∈ V, ∀ z, q w z ∈ U)
    (hpeq : ∀ w ∈ V, ∀ z, p (q w z) z = v w z) :
    ContinuousOn (Function.uncurry q) (V ×ˢ univ) := by
  intro w hw
  have hp0 : Continuous (fun z => p (q w.1 w.2) z) :=
    hp.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hq w.1 hw.1 w.2, mem_univ z⟩)
  have hc : ContinuousWithinAt
      (fun w' : ℂ × Z => (L : ℝ) * dist (v w'.1 w'.2) (p (q w.1 w.2) w'.2))
      (V ×ˢ univ) w :=
    continuousWithinAt_const.mul ((hv w hw).dist (hp0.comp continuous_snd).continuousWithinAt)
  have ht : Tendsto
      (fun w' : ℂ × Z => (L : ℝ) * dist (v w'.1 w'.2) (p (q w.1 w.2) w'.2))
      (𝓝[V ×ˢ univ] w) (𝓝 0) := by
    simpa only [hpeq w.1 hw.1 w.2, dist_self, mul_zero] using hc.tendsto
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_ ht
  exact Filter.Eventually.mono self_mem_nhdsWithin (fun t ht => by
    simpa only [Function.uncurry, hpeq t.1 ht.1 t.2] using
      hbound t.2 (q t.1 t.2) (hq t.1 ht.1 t.2) (q w.1 w.2) (hq w.1 hw.1 w.2))

/-- Nonvanishing of the derivatives at the center extends to one uniform disk. -/
theorem exists_uniform_deriv_ne_zero {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hne : ∀ z, deriv (fun t => p t z) a ≠ 0) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ t ∈ ball a r, ∀ z, deriv (fun u => p u z) t ≠ 0 := by
  have hDp := continuousOn_deriv_family hG hp hd
  have hnear : ∀ᶠ t in 𝓝 a, ∀ z ∈ (univ : Set Z), deriv (fun u => p u z) t ≠ 0 :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun z _ =>
      (hDp.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).tendsto.eventually
        (eventually_ne_nhds (hne z)))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hnear.and (hG.mem_nhds ha))
  exact ⟨r, hr, fun t ht => (hb t ht).2, fun t ht z => (hb t ht).1 z (mem_univ z)⟩

/-- The inverse of a map approximating the identity with error one half has
Lipschitz constant at most two. -/
theorem dist_le_of_approximates_id_half {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id ℂ ℂ) (ball a r) (1 / 2))
    {x y : ℂ} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
    dist x y ≤ 2 * dist (f x) (f y) := by
  have h := (hf.antilipschitzWith (f' := ContinuousLinearEquiv.refl ℂ ℂ)
    (Or.inr (by norm_num))).le_mul_dist ⟨x, hx⟩ ⟨y, hy⟩
  norm_num at h
  exact h

/-- A neighborhood of all values at a fixed point contains the image of one
common disk, uniformly over a compact parameter space. -/
theorem exists_uniform_mapsTo_nhds {G V : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hV : IsOpen V) (hpa : ∀ z, p a z ∈ V) :
    ∃ r > 0, ball a r ⊆ G ∧ ∀ z, MapsTo (fun t => p t z) (ball a r) V := by
  have hnear : ∀ᶠ t in 𝓝 a, ∀ z ∈ (univ : Set Z), p t z ∈ V :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun z _ =>
      (hp.continuousAt ((hG.prod isOpen_univ).mem_nhds ⟨ha, mem_univ z⟩)).tendsto.eventually
        (hV.mem_nhds (hpa z)))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hnear.and (hG.mem_nhds ha))
  exact ⟨r, hr, fun t ht => (hb t ht).2, fun z t ht => (hb t ht).1 z (mem_univ z)⟩

/-- The last assertion in Neuschel's Lemma 2.2(iv), in a stronger form:
the intersection of the images of every positive-radius disk is a neighborhood
of zero. -/
theorem zero_mem_interior_iInter_image_ball {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    [CompactSpace Z] {p : ℂ → Z → ℂ}
    (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    (hz : ∀ z, p a z = 0) (hne : ∀ z, deriv (fun t => p t z) a ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    (0 : ℂ) ∈ interior (⋂ z, (fun t => p t z) '' ball a ε) := by
  obtain ⟨r, hr, δ, hδ, hU, _, _, hS⟩ := exists_uniform_image_disk
    (hG.inter isOpen_ball) ⟨ha, mem_ball_self hε⟩
    (hp.mono (Set.prod_mono inter_subset_left Subset.rfl))
    (fun z => (hd z).mono inter_subset_left) hz hne
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ball_mem_nhds 0 hδ)
    (fun w hw => mem_iInter.mpr (fun z =>
      image_mono (fun t ht => (hU ht).2) (hS z (ball_subset_closedBall hw)))))

end Neuschel
