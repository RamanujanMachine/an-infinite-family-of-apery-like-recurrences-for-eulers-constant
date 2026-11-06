module

public import Neuschel.LocalExpansion

/-! The explicit leading term at a nondegenerate saddle. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

theorem exists_uniform_quadratic_root_bounds {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {b : Z → ℂ} (hb : Continuous b) (hb0 : ∀ z, b z ≠ 0) {v : ℂ} (hv : v ≠ 0) :
    ∃ B ≥ 1, ∀ z, ‖leadingRoot 2 v (b z)‖ ≤ B ∧ ‖(leadingRoot 2 v (b z))⁻¹‖ ≤ B := by
  obtain ⟨B₁, hB₁⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_univ.exists_bound_of_continuousOn (hb.inv₀ hb0).continuousOn
  let B := max 1 (max B₁ B₂)
  have hB : 1 ≤ B := le_max_left _ _
  have h₁ : B₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : B₂ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hnorm : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ B → x ≤ B := by
    intro x hx hx2
    by_cases h : x ≤ 1
    · exact h.trans hB
    · nlinarith [mul_nonneg (show 0 ≤ x - 1 by linarith) hx]
  refine ⟨B, hB, fun z => ?_⟩
  have hs : ‖leadingRoot 2 v (b z)‖ ^ 2 = ‖b z‖ := by
    rw [← norm_pow, leadingRoot_pow (by decide) hv (hb0 z)]
  have hi : ‖(leadingRoot 2 v (b z))⁻¹‖ ^ 2 = ‖(b z)⁻¹‖ := by
    rw [norm_inv, inv_pow, hs, norm_inv]
  exact ⟨hnorm _ (norm_nonneg _) (hs.le.trans ((hB₁ z (mem_univ z)).trans h₁)),
    hnorm _ (norm_nonneg _) (hi.le.trans ((hB₂ z (mem_univ z)).trans h₂))⟩

namespace LocalContourModel

variable {Z : Type*} [TopologicalSpace Z] {μ : ℕ} {a v : ℂ}
  {b : Z → ℂ} {P : ℂ → Z → ℂ} {G : Set ℂ} {γ : ℝ → ℂ}

theorem quadratic_leading_estimate [CompactSpace Z] {v : ℂ} {b : Z → ℂ}
    {P : ℂ → Z → ℂ} {G : Set ℂ}
    (M : LocalContourModel 2 0 v b P G (fun s : ℝ => (s : ℂ) * v))
    (hG : IsOpen G) (h0 : (0 : ℂ) ∈ G) (hv : v ≠ 0)
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    {q : ℂ → Z → ℂ} (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ z,
      ‖(∫ s in 0..M.cutoff, v *
        (Complex.exp (-(R : ℂ) * (P ((s : ℂ) * v) z - P 0 z)) * q ((s : ℂ) * v) z)) -
        q 0 z * (leadingRoot 2 v (b z))⁻¹ * (2 : ℂ)⁻¹ *
          ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ C * R ^ (-1 : ℝ) := by
  have hs (z : Z) : ∀ᶠ t in 𝓝 (0 : ℂ), HasSum
      (fun n => (iteratedDeriv n (fun t => q t z) 0 / (n.factorial : ℂ)) *
        (t - 0) ^ (0 + n)) (q t z) := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm] using
      hasFPowerSeriesAt_iff'.mp ((hdq z).analyticAt (hG.mem_nhds h0)).hasFPowerSeriesAt
  obtain ⟨H, _, _, hH0, _, hbound⟩ := M.local_expansion (by decide) hG h0 0 hdP hq hdq hs
    (by simp) (Complex.continuous_ofReal.mul continuous_const).continuousOn
    continuous_const.continuousOn
    (fun s _ => by simpa using Complex.ofRealCLM.hasDerivAt.mul_const v)
  obtain ⟨C, hC, hb⟩ := hbound 1
  refine ⟨C, hC, hb.mono (fun R hR z => ?_)⟩
  simpa [phaseQuotient, hH0, iteratedDeriv_zero, M.deriv_inverse_center hG h0 hv] using hR z

theorem two_sided_quadratic_leading_estimate [CompactSpace Z] {v : ℂ} {b : Z → ℂ}
    {P : ℂ → Z → ℂ} {G : Set ℂ}
    (Mplus : LocalContourModel 2 0 v b P G (fun s : ℝ => (s : ℂ) * v))
    (Mminus : LocalContourModel 2 0 (-v) b P G (fun s : ℝ => (s : ℂ) * (-v)))
    (hG : IsOpen G) (h0 : (0 : ℂ) ∈ G) (hv : v ≠ 0)
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    {q : ℂ → Z → ℂ} (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ z,
      ‖((∫ s in 0..Mplus.cutoff, v *
          (Complex.exp (-(R : ℂ) * (P ((s : ℂ) * v) z - P 0 z)) * q ((s : ℂ) * v) z)) -
        (∫ s in 0..Mminus.cutoff, (-v) *
          (Complex.exp (-(R : ℂ) * (P ((s : ℂ) * (-v)) z - P 0 z)) * q ((s : ℂ) * (-v)) z))) -
        q 0 z * (leadingRoot 2 v (b z))⁻¹ *
          ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ C * R ^ (-1 : ℝ) := by
  obtain ⟨Cplus, hCplus, hbplus⟩ := Mplus.quadratic_leading_estimate hG h0 hv hdP hq hdq
  obtain ⟨Cminus, hCminus, hbminus⟩ := Mminus.quadratic_leading_estimate hG h0 (neg_ne_zero.mpr hv) hdP hq hdq
  refine ⟨Cplus + Cminus, add_nonneg hCplus hCminus, ?_⟩
  filter_upwards [hbplus, hbminus] with R hRplus hRminus z
  have hb := (norm_sub_le _ _).trans (add_le_add (hRplus z) (hRminus z))
  convert hb using 1
  · congr 1
    have he : leadingRoot 2 (-v) (b z) = -leadingRoot 2 v (b z) := by
      simp [leadingRoot, div_neg]
    rw [he, inv_neg]
    ring
  · ring

end LocalContourModel

end Neuschel
