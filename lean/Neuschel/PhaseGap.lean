module

public import Neuschel.UniformLocal
public import Mathlib.Topology.Order.Compact

/-! The uniform positive phase gap on the nonlocal part of a contour. -/

public section

namespace Neuschel

open Set Filter
open scoped Topology

/-- Pointwise strict phase positivity, compactness of the parameter space, and
the uniform endpoint lower bound imply one positive gap on every contour tail. -/
theorem uniform_gap_on_tail {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
    {f : ℝ → Z → ℝ} (hf : ContinuousOn (Function.uncurry f) (Ioo 0 1 ×ˢ univ))
    (hpos : ∀ s ∈ Ioo 0 1, ∀ z, 0 < f s z)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ f s z)
    {δ : ℝ} (hδ : δ ∈ Ioo 0 1) :
    ∃ ε > 0, ∀ s ∈ Ico δ 1, ∀ z, ε ≤ f s z := by
  obtain ⟨r, hr, η, hη, hend⟩ := hend
  have hsub : Icc δ (max δ r) ×ˢ (univ : Set Z) ⊆ Ioo 0 1 ×ˢ univ :=
    fun w hw => ⟨⟨hδ.1.trans_le hw.1.1, hw.1.2.trans_lt (max_lt hδ.2 hr)⟩, hw.2⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_Icc.prod (isCompact_univ (X := Z))).exists_isMinOn
    (show (Icc δ (max δ r) ×ˢ (univ : Set Z)).Nonempty from
      ⟨(δ, Classical.choice inferInstance), ⟨⟨le_rfl, le_max_left _ _⟩, mem_univ _⟩⟩)
    (hf.mono hsub)
  refine ⟨min (f w.1 w.2) η, lt_min (hpos w.1 (hsub hw).1 w.2) hη, fun s hs z => ?_⟩
  exact (le_or_gt s (max δ r)).elim
    (fun h => (min_le_left _ _).trans (show f w.1 w.2 ≤ f s z by
      simpa only [Set.mem_ofPred_eq, Function.uncurry_def] using
        hmin (show (s, z) ∈ Icc δ (max δ r) ×ˢ univ from ⟨⟨hs.1, h⟩, mem_univ z⟩)))
    (fun h => (min_le_right _ _).trans (hend s ⟨(le_max_right δ r).trans_lt h, hs.2⟩ z))

end Neuschel
