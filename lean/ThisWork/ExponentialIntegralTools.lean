module

public import ThisWork.LogDecayTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric MeasureTheory
open scoped Topology

theorem integral_norm_le_exp_tail {f : ℝ → ℂ} {C a T : ℝ} (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi T)))
    (hb : ∀ t ∈ Ioi T, ‖f t‖ ≤ C * Real.exp (-a * t)) :
    IntegrableOn f (Ioi T) ∧
      ‖∫ t in Ioi T, f t‖ ≤ C * Real.exp (-a * T) / a := by
  have hg : IntegrableOn (fun t => C * Real.exp (-a * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) T).const_mul C
  have hfa : IntegrableOn f (Ioi T) := hg.mono' hf
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hb t ht)
  refine ⟨hfa, ?_⟩
  calc
    _ ≤ ∫ t in Ioi T, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, C * Real.exp (-a * t) :=
      integral_mono_ae hfa.norm hg ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hb t ht)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
      ring

theorem integral_norm_le_shifted_exp_tail {f : ℝ → ℂ} {C a T : ℝ} (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi T)))
    (hb : ∀ t ∈ Ioi T, ‖f t‖ ≤ C * Real.exp (-a * (t - T))) :
    IntegrableOn f (Ioi T) ∧ ‖∫ t in Ioi T, f t‖ ≤ C / a := by
  have h := integral_norm_le_exp_tail ha hf
    (C := C * Real.exp (a * T)) (fun t ht => by
      convert hb t ht using 1
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [mul_assoc, ← Real.exp_add, show a * T + -a * T = 0 by ring, Real.exp_zero, mul_one]

end ThisWork.Analytic
