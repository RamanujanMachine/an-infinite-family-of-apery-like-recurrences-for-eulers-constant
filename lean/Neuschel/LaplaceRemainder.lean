module

public import Neuschel.LaplaceMoment

/-! Integrated remainder bounds for the local Laplace expansion. -/

public section

namespace Neuschel

open Set Filter MeasureTheory
open scoped Topology

/-- A power bound on the transformed remainder gives the required Laplace
order, with an explicit Gamma constant independent of the complex ray. -/
theorem norm_laplace_remainder_le {s n η M : ℝ} (hs : 0 < s) (hn : 0 < n) (hη : 0 < η)
    (hM : 0 ≤ M) {z : ℂ} (hz : η ≤ z.re) {F : ℝ → ℂ}
    (hF : ∀ t ∈ Ioc (0 : ℝ) 1, ‖F t‖ ≤ M * t ^ (s - 1)) :
    ‖∫ t : ℝ in 0..1, Complex.exp (-((n : ℂ) * z) * (t : ℂ)) * F t‖ ≤
      M * ((1 / (n * η)) ^ s * Real.Gamma s) := by
  let g : ℝ → ℝ := fun t => t ^ (s - 1) * Real.exp (-(n * η) * t)
  have hg : IntegrableOn g (Ioi 0) := by
    simpa only [g, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (by linarith : -1 < s - 1) zero_lt_one (mul_pos hn hη)
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖Complex.exp (-((n : ℂ) * z) * (t : ℂ)) * F t‖ ≤ M * g t := by
    intro t ht
    have he : ‖Complex.exp (-((n : ℂ) * z) * (t : ℂ))‖ ≤ Real.exp (-(n * η) * t) := by
      simpa [Complex.norm_exp] using Real.exp_le_exp.mpr
        (show -(n * z.re) * t ≤ -(n * η) * t from by
          nlinarith [mul_nonneg (mul_nonneg hn.le ht.1.le) (sub_nonneg.mpr hz)])
    simpa only [g, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul he (hF t ht) (norm_nonneg _) (Real.exp_nonneg _)
  have hb := norm_integral_le_of_norm_le
    ((show IntegrableOn (fun t => M * g t) (Ioi 0) volume from hg.const_mul M).mono_set Ioc_subset_Ioi_self)
    ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hpoint t ht))
  have hm : (∫ t : ℝ in Ioc 0 1, M * g t) ≤ ∫ t : ℝ in Ioi 0, M * g t :=
    setIntegral_mono_set (hg.const_mul M)
      ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => mul_nonneg hM
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))))
      (Eventually.of_forall (fun t ht => ht.1))
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine (hb.trans hm).trans_eq ?_
  rw [integral_const_mul]
  simpa only [g, neg_mul] using congrArg (fun x : ℝ => M * x)
    (Real.integral_rpow_mul_exp_neg_mul_Ioi hs (mul_pos hn hη))

end Neuschel
