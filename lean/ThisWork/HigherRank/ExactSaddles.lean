module

public import ThisWork.HigherRank.SaddleEquation
public import ThisWork.HigherRank.Regions
public import ThisWork.SaddleStability

/-! Stability of every off-cut limiting saddle of the actual arbitrary-rank
Gamma kernel, with the quantitative displacement `O(n^(-1/r))`. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem exists_exact_saddle {r : ℕ} (hr : 3 ≤ r) {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ) {ζ : ℂ}
    (hζ : ζ ∈ Complex.slitPlane) (hz : limitingEquation r A z j ζ = 0) :
    ∃ δ > 0, ball ζ δ ⊆ Complex.slitPlane ∧ ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∃ s ∈ ball ζ δ, exactSaddleEquation r A z j n s = 0 ∧
        deriv (exactSaddleEquation r A z j n) s ≠ 0 ∧
        ‖s - ζ‖ ≤ C * smallParameter r n ∧
        ∀ t ∈ ball ζ δ, exactSaddleEquation r A z j n t = 0 → t = s := by
  obtain ⟨δ, hδ, κ, hκ, η, hη, M, hM, hregion⟩ := exists_local_slit_region hζ
  obtain ⟨C, hC, hb⟩ := uniform_exactSaddleEquation_region hr hA z j hκ hη hM
  have hslit : ball ζ δ ⊆ Complex.slitPlane := fun s hs =>
    region_mem_slitPlane hκ hη (hregion s (ball_subset_closedBall hs)).2
  have hF : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (exactSaddleEquation r A z j n) (ball ζ δ) := by
    filter_upwards [eventually_scaled_region_in_kernelDomain (by omega : 0 < r) hA hκ hη M]
      with n hn
    apply (differentiableOn_exactSaddleEquation r A z j n).mono
    intro s hs
    have hg := hregion s (ball_subset_closedBall hs)
    exact hn s ((Complex.re_le_norm s).trans hg.1) hg.2
  have hf : DifferentiableOn ℂ (limitingEquation r A z j) (ball ζ δ) := fun s hs =>
    (hasDerivAt_limitingEquation r A z j (hslit hs)).differentiableAt.differentiableWithinAt
  have hlim : TendstoUniformlyOn (fun n => exactSaddleEquation r A z j n)
      (limitingEquation r A z j) atTop (ball ζ δ) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he : Tendsto (fun n => C * smallParameter r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (smallParameter_tendsto (show 0 < r by omega)).const_mul C
    filter_upwards [hb, he.eventually_lt_const hε] with n hn hεn s hs
    rw [dist_eq_norm, norm_sub_rev]
    have hg := hregion s (ball_subset_closedBall hs)
    exact (hn s hg.1 hg.2).trans_lt hεn
  have hd : deriv (limitingEquation r A z j) ζ ≠ 0 := by
    rw [(hasDerivAt_limitingEquation r A z j hζ).deriv]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (show r ≠ 0 by omega)) (Complex.slitPlane_ne_zero hζ)
  have hbound : ∀ᶠ n : ℕ in atTop, ‖exactSaddleEquation r A z j n ζ‖ ≤ C * smallParameter r n := by
    filter_upwards [hb] with n hn
    have hg := hregion ζ (mem_closedBall_self hδ.le)
    simpa only [hz, sub_zero] using hn ζ hg.1 hg.2
  obtain ⟨d, hdpos, hdsub, K, hK, hzeros⟩ := Analytic.exists_simple_zero_with_rate
    isOpen_ball (mem_ball_self hδ) hF hf hlim.tendstoLocallyUniformlyOn hz hd hC hbound
  exact ⟨d, hdpos, hdsub.trans hslit, K, hK, hzeros⟩

theorem exists_exact_saddle_at_angle {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (j : ℤ) {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi)
    (hj : (r : ℝ) * θ = -2 * Real.pi * j) :
    ∃ δ > 0, ball ((saddleScale r A z : ℂ) * Phase.rho θ) δ ⊆ Complex.slitPlane ∧
      ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ s ∈ ball ((saddleScale r A z : ℂ) * Phase.rho θ) δ,
        exactSaddleEquation r A z j n s = 0 ∧ deriv (exactSaddleEquation r A z j n) s ≠ 0 ∧
        ‖s - (saddleScale r A z : ℂ) * Phase.rho θ‖ ≤ C * smallParameter r n ∧
        ∀ t ∈ ball ((saddleScale r A z : ℂ) * Phase.rho θ) δ,
          exactSaddleEquation r A z j n t = 0 → t = s := by
  have hc := saddleScale_pos hA hz
  have hζ : (saddleScale r A z : ℂ) * Phase.rho θ ∈ Complex.slitPlane := by
    apply (ThisWork.div_pos_real_mem_slitPlane_iff hc _).mp
    simpa only [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hc.ne')] using Phase.rho_mem_slitPlane hθ
  apply exists_exact_saddle hr hA z j hζ
  rw [limitingEquation_eq_phase (by omega : 0 < r) hA hz j hj (Complex.slitPlane_ne_zero hζ)]
  exact Phase.equation_saddle r hθ hc

end ThisWork.HigherRank
