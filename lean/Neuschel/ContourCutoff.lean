module

public import Neuschel.RootBranch
public import Mathlib.Topology.Order.Compact

/-! Uniform initial contour intervals and endpoint bounds. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

/-- A right-neighborhood property, valid also at zero, holds on a closed
initial interval. The endpoint can be included by shrinking the neighborhood. -/
theorem exists_closed_initial_interval {P : ℝ → Prop}
    (hP : ∀ᶠ s : ℝ in 𝓝[>] 0, P s) (h0 : P 0) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) δ, P s := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hP)
  refine ⟨r / 2, half_pos hr, fun s hs => ?_⟩
  exact (eq_or_lt_of_le hs.1).elim (fun he => he ▸ h0) (fun hpos => hb s
    (by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1] using
      hs.2.trans_lt (half_lt_self hr)) hpos)

theorem exists_positive_re_gap {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
    {α : Z → ℂ} (hα : Continuous α) (hpos : ∀ z, 0 < (α z).re) :
    ∃ η > 0, ∀ z, η ≤ (α z).re := by
  obtain ⟨z, _, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set Z).Nonempty)
    (Complex.continuous_re.comp hα).continuousOn
  exact ⟨(α z).re, hpos z, fun w => by
    simpa only [Set.mem_ofPred_eq, Function.comp_def] using hmin (mem_univ w)⟩

/-- Choose a single initial contour interval whose images lie in a smaller
target disk, preserving any additional eventual branch identity. -/
theorem LocalInverseFamily.exists_common_contour_cutoff {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] {p : ℂ → Z → ℂ} {a : ℂ} {G : Set ℂ} (e : LocalInverseFamily p a G)
    (hp : ContinuousOn (Function.uncurry p) (ball a e.sourceRadius ×ˢ univ))
    (hz : ∀ z, p a z = 0) {γ : ℝ → ℂ}
    (hend : Tendsto γ (𝓝[>] 0) (𝓝 a)) (hγ0 : γ 0 = a)
    {B : ℝ → Prop} (hB : ∀ᶠ s : ℝ in 𝓝[>] 0, B s) :
    ∃ δ ∈ Ioo (0 : ℝ) 1,
      (∀ s ∈ Icc (0 : ℝ) δ, ∀ z, γ s ∈ e.source z ∧
        p (γ s) z ∈ ball 0 (e.targetRadius / 2)) ∧ ∀ s ∈ Ioc (0 : ℝ) δ, B s := by
  obtain ⟨ε, hε, hsource, hmap⟩ := exists_uniform_mapsTo_nhds (V := ball (0 : ℂ) (e.targetRadius / 2)) isOpen_ball
    (mem_ball_self e.sourceRadius_pos) hp isOpen_ball
    (fun z => by simpa only [hz z] using mem_ball_self (half_pos e.targetRadius_pos))
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 ∧ γ s ∈ ball a ε ∧ (0 < s → B s) := by
    filter_upwards [hend.eventually (ball_mem_nhds a hε), hB,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with s hs hBs hs1
    exact ⟨hs1, hs, fun _ => hBs⟩
  obtain ⟨δ, hδ, hgood⟩ := exists_closed_initial_interval hnear
    ⟨zero_lt_one, by simpa only [hγ0] using (mem_ball_self hε : a ∈ ball a ε),
      fun hs => (lt_irrefl (0 : ℝ) hs).elim⟩
  exact ⟨δ, ⟨hδ, (hgood δ (right_mem_Icc.mpr hδ.le)).1⟩,
    (fun s hs z => ⟨⟨hsource (hgood s hs).2.1,
      ball_subset_ball (half_le_self e.targetRadius_pos.le) (hmap z (hgood s hs).2.1)⟩,
      hmap z (hgood s hs).2.1⟩),
    fun s hs => (hgood s ⟨hs.1.le, hs.2⟩).2.2 hs.1⟩

end Neuschel
