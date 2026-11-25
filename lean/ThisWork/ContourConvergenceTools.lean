module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import ThisWork.PolynomialTailTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter MeasureTheory
open scoped Topology

theorem integrableOn_Iic_of_exp_bound {f : ℝ → ℂ} {r : ℝ}
    (hf : ContinuousOn f (Iic r)) (hb : ∀ᶠ u : ℝ in atBot, ‖f u‖ ≤ Real.exp u) :
    IntegrableOn f (Iic r) := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp hb
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr
    ⟨⟨Iic (min a r), Iic_mem_atBot _, ?_⟩, hf.locallyIntegrableOn measurableSet_Iic⟩
  exact (integrableOn_exp_Iic _).mono'
    ((hf.mono (Iic_subset_Iic.mpr (min_le_right a r))).aestronglyMeasurable measurableSet_Iic)
    ((ae_restrict_mem measurableSet_Iic).mono fun u hu => ha u (hu.trans (min_le_left a r)))

end ThisWork.Analytic
