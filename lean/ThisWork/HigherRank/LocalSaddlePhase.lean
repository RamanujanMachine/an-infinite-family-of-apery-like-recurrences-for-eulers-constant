module

public import ThisWork.HigherRank.KernelApproximation

/-! Exact local phases at the moving arbitrary-rank Gamma saddles, together
with the quantitative comparison to the limiting phase. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem eventually_exists_exact_local_phase {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ)
    {ζ : ℂ} (hζ : ζ ∈ Complex.slitPlane) (hz : limitingEquation r A z j ζ = 0) :
    ∃ δ > 0, ball ζ δ ⊆ Complex.slitPlane ∧ ∃ C ≥ 0, ∃ D ≥ 0,
      ∀ᶠ n : ℕ in atTop, ∃ a ∈ ball ζ δ,
        exactSaddleEquation r A z j n a = 0 ∧ deriv (exactSaddleEquation r A z j n) a ≠ 0 ∧
        ‖a - ζ‖ ≤ C * smallParameter r n ∧
        ∃ p : ℂ → ℂ, p a = 0 ∧ deriv p a = 0 ∧ deriv (deriv p) a ≠ 0 ∧
          (∀ s ∈ ball ζ δ, HasDerivAt p (-exactSaddleEquation r A z j n s) s) ∧
          (∀ s ∈ ball ζ δ,
            kernel r b A z j n ((largeScale r n : ℂ) * s) =
              kernel r b A z j n ((largeScale r n : ℂ) * a) *
                Complex.exp (-(largeScale r n : ℂ) * p s)) ∧
          ∀ s ∈ ball ζ δ,
            ‖p s + limitingPhase r A z j s - limitingPhase r A z j a‖ ≤
              ‖s - a‖ * (D * smallParameter r n) := by
  obtain ⟨δ, hδ, κ, hκ, η, hη, M, hM, hregion⟩ := exists_local_slit_region hζ
  have hslit : ball ζ δ ⊆ Complex.slitPlane := fun s hs =>
    region_mem_slitPlane hκ hη (hregion s (ball_subset_closedBall hs)).2
  obtain ⟨_, _, _, C, hC, hzeros⟩ := exists_exact_saddle hr hA z j hζ hz
  obtain ⟨D, hD, herror⟩ := uniform_exactSaddleEquation_region hr hA z j hκ hη hM
  have hsmall : ∀ᶠ n : ℕ in atTop, C * smallParameter r n < δ := by
    have ht : Tendsto (fun n => C * smallParameter r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (smallParameter_tendsto (show 0 < r by omega)).const_mul C
    exact ht.eventually_lt_const hδ
  refine ⟨δ, hδ, hslit, C, hC, D, hD, ?_⟩
  filter_upwards [hzeros, hsmall, herror,
    eventually_scaled_slit_in_kernelDomain (by omega : 0 < r) hA M,
    eventually_gt_atTop (0 : ℕ)] with n hn hnear herr hdom hn0
  obtain ⟨a, _, ha0, haderiv, hdist, _⟩ := hn
  have ha : a ∈ ball ζ δ := by
    simpa only [mem_ball, dist_eq_norm] using hdist.trans_lt hnear
  have hmap : MapsTo (fun s : ℂ => (largeScale r n : ℂ) * s) (ball ζ δ) (kernelDomain r A n) := by
    intro s hs
    exact hdom s ((Complex.re_le_norm s).trans (hregion s (ball_subset_closedBall hs)).1) (hslit hs)
  obtain ⟨p, hpa, hp, hkernel⟩ := exists_scaled_kernel_phase b z j hn0 ha hmap
  have hsimple := Analytic.phase_simple_saddle ha hp ha0 haderiv
  refine ⟨a, ha, ha0, haderiv, hdist, p, hpa, hsimple.1, hsimple.2, hp, hkernel, ?_⟩
  intro s hs
  apply norm_local_phase_error ha hs hpa hslit hmap hp
  intro t ht
  have hg := hregion t (ball_subset_closedBall ht)
  exact herr t hg.1 hg.2

end ThisWork.HigherRank
