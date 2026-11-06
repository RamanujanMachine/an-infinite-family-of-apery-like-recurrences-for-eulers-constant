module

public import Neuschel.LocalWatson
public import Neuschel.LocalContour
public import Neuschel.ChangeOfVariable

/-! Uniform expansion of the original local contour integral. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

variable {Z : Type*} [TopologicalSpace Z]

namespace LocalContourModel

variable {μ : ℕ} {a v : ℂ} {b : Z → ℂ} {P : ℂ → Z → ℂ}
  {G : Set ℂ} {γ : ℝ → ℂ}

theorem deriv_inverse_center (M : LocalContourModel μ a v b P G γ)
    (hG : IsOpen G) (ha : a ∈ G) (hv : v ≠ 0) (z : Z) :
    deriv (fun w => M.inverseFamily.inverse w z) 0 = (leadingRoot μ v (b z))⁻¹ := by
  exact M.inverseFamily.deriv_inverse_center (saddleCoordinate_center μ a _ M.factor)
    (fun z => hasDerivAt_saddleCoordinate_center μ a _
      ((M.factor_holomorphic z).differentiableAt (hG.mem_nhds ha)) (M.factor_center z))
    (fun z => leadingRoot_ne_zero μ hv (b z)) z

/-- The original centered local contour integral equals its straightened ray
integral, with the branch fixed by the outgoing contour. -/
theorem local_integral_eq_segment (M : LocalContourModel μ a v b P G γ) (κ : ℂ)
    {q : ℂ → Z → ℂ} (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G)
    (hγ0 : γ 0 = a) {velocity : ℝ → ℂ}
    (hc : ContinuousOn γ (Icc 0 M.cutoff))
    (hv : ContinuousOn velocity (Icc 0 M.cutoff))
    (hdγ : ∀ s ∈ Ioo 0 M.cutoff, HasDerivAt γ (velocity s) s) (z : Z) :
    (∫ s in 0..M.cutoff, velocity s *
      (Complex.exp (-κ * (P (γ s) z - P a z)) * q (γ s) z)) =
    segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * M.inverseFamily.amplitude q w z)
      0 (normalizedRoot μ (P (γ M.cutoff) z - P a z)) := by
  have h := M.inverseFamily.laplace_contour_substitution κ μ hdP hdq M.phase_inverse
    M.cutoff_mem.1.le hc hv hdγ z (fun s hs => M.contour_in_source s hs z)
  simpa only [hγ0, saddleCoordinate_center,
    M.principal_root M.cutoff (right_mem_Ioc.mpr M.cutoff_mem.1) z] using h

/-- All orders of the uniform expansion of the original local contour integral.
The analytic coefficient function is chosen once, independently of the order. -/
theorem local_expansion [CompactSpace Z] (M : LocalContourModel μ a v b P G γ)
    (hμ : μ ≠ 0) (hG : IsOpen G) (ha : a ∈ G) (k : ℕ)
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    {q : ℂ → Z → ℂ} (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {c : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z))
    (hγ0 : γ 0 = a) {velocity : ℝ → ℂ}
    (hc : ContinuousOn γ (Icc 0 M.cutoff))
    (hv : ContinuousOn velocity (Icc 0 M.cutoff))
    (hdγ : ∀ s ∈ Ioo 0 M.cutoff, HasDerivAt γ (velocity s) s) :
    ∃ H : ℂ → Z → ℂ,
      ContinuousOn (Function.uncurry H) (ball 0 M.inverseFamily.targetRadius ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun w => H w z) (ball 0 M.inverseFamily.targetRadius)) ∧
      (∀ z, H 0 z = c 0 z * deriv (fun w => M.inverseFamily.inverse w z) 0 ^ (k + 1)) ∧
      H = M.inverseFamily.amplitudeFactor k (phaseQuotient k a q) ∧
      ∀ m : ℕ, ∃ C ≥ 0, ∀ᶠ n : ℝ in atTop, ∀ z,
        ‖(∫ s in 0..M.cutoff, velocity s *
            (Complex.exp (-(n : ℂ) * (P (γ s) z - P a z)) * q (γ s) z)) -
          ∑ j ∈ Finset.range m, phaseQuotient j 0 H 0 z * (μ : ℂ)⁻¹ *
            ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
              n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)‖ ≤
        C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) := by
  obtain ⟨H, hH, hdH, hfactor, hcenter, hcanonical⟩ :=
    M.inverseFamily.exists_amplitude_factor_from_expansion k hG ha
      (saddleCoordinate_center μ a _ M.factor) hq hdq hs
  refine ⟨H, hH, hdH, hcenter, hcanonical, fun m => ?_⟩
  have hρ : ∀ z, ‖normalizedRoot μ (P (γ M.cutoff) z - P a z)‖ ≤
      M.inverseFamily.targetRadius / 2 := fun z => by
    rw [← M.principal_root M.cutoff (right_mem_Ioc.mpr M.cutoff_mem.1) z]
    exact (show ‖saddleCoordinate μ a (fun z => leadingRoot μ v (b z)) M.factor (γ M.cutoff) z‖ <
      M.inverseFamily.targetRadius / 2 from by
        simpa only [mem_ball, dist_zero_right] using
          M.image_small M.cutoff (right_mem_Icc.mpr M.cutoff_mem.1.le) z).le
  obtain ⟨C, hC, hbound⟩ := uniform_local_watson hμ m k
    (le_of_lt (half_pos M.inverseFamily.targetRadius_pos))
    (half_lt_self M.inverseFamily.targetRadius_pos) M.endpoint_gap_pos hH hdH
    M.endpoint_phase_continuous M.endpoint_gap_le hρ
  refine ⟨C, hC, hbound.mono (fun n hn z => ?_)⟩
  rw [M.local_integral_eq_segment (n : ℂ) hdP hdq hγ0 hc hv hdγ z]
  have heq := segmentIntegral_congr_ball
    (fun w hw => congrArg (fun u : ℂ => Complex.exp (-(n : ℂ) * w ^ μ) * u) (hfactor w hw z))
    (mem_ball_self M.inverseFamily.targetRadius_pos)
    (show normalizedRoot μ (P (γ M.cutoff) z - P a z) ∈ ball 0 M.inverseFamily.targetRadius from by
      simpa only [mem_ball, dist_zero_right] using
        (hρ z).trans_lt (half_lt_self M.inverseFamily.targetRadius_pos))
  simpa only [heq, mul_assoc] using hn z

end LocalContourModel

end Neuschel
