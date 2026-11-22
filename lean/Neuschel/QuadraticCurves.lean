module

public import Neuschel.QuadraticExpansion

/-! Quadratic leading estimates for curved local contours. These are direct
specializations of the already proved uniform local expansion. -/

public section
namespace Neuschel.LocalContourModel

open Set Filter Metric
open scoped Topology

theorem quadratic_curve_leading_estimate {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {v : ℂ} {b : Z → ℂ} {P : ℂ → Z → ℂ} {G : Set ℂ} {γ velocity : ℝ → ℂ}
    (M : Neuschel.LocalContourModel 2 0 v b P G γ)
    (hG : IsOpen G) (h0 : (0 : ℂ) ∈ G) (hv : v ≠ 0)
    (hdP : ∀ q, DifferentiableOn ℂ (fun t => P t q) G)
    {amplitude : ℂ → Z → ℂ}
    (hq : ContinuousOn (Function.uncurry amplitude) (G ×ˢ univ))
    (hdq : ∀ q, DifferentiableOn ℂ (fun t => amplitude t q) G)
    (hγ0 : γ 0 = 0) (hc : ContinuousOn γ (Icc 0 M.cutoff))
    (hvel : ContinuousOn velocity (Icc 0 M.cutoff))
    (hdγ : ∀ t ∈ Ioo 0 M.cutoff, HasDerivAt γ (velocity t) t) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ q,
      ‖(∫ t in 0..M.cutoff, velocity t *
        (Complex.exp (-(R : ℂ) * (P (γ t) q - P 0 q)) * amplitude (γ t) q)) -
        amplitude 0 q * (leadingRoot 2 v (b q))⁻¹ * (2 : ℂ)⁻¹ *
          ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ C * R ^ (-1 : ℝ) := by
  have hs (q : Z) : ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => (iteratedDeriv n (fun t => amplitude t q) 0 / (n.factorial : ℂ)) *
        (t - 0) ^ (0 + n)) (amplitude t q) := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm] using
      hasFPowerSeriesAt_iff'.mp ((hdq q).analyticAt (hG.mem_nhds h0)).hasFPowerSeriesAt
  obtain ⟨H, _, _, hH0, _, hbound⟩ := M.local_expansion (by decide) hG h0 0 hdP hq hdq hs
    hγ0 hc hvel hdγ
  obtain ⟨C, hC, hb⟩ := hbound 1
  refine ⟨C, hC, hb.mono (fun R hR q => ?_)⟩
  simpa [phaseQuotient, hH0, iteratedDeriv_zero, M.deriv_inverse_center hG h0 hv] using hR q

end Neuschel.LocalContourModel
