module

public import ThisWork.HigherRank.LocalSaddlePhase
public import ThisWork.CompactFamily

/-! The actual arbitrary-rank saddle equations and their limit as a jointly
continuous holomorphic family with compact parameter space `OnePoint ℕ`. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology OnePoint

theorem exists_compact_equation_neighborhood {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {ζ : ℂ} (hζ : ζ ∈ Complex.slitPlane) :
    ∃ δ > 0, ball ζ δ ⊆ Complex.slitPlane ∧ ∀ᶠ N : ℕ in atTop,
      ContinuousOn (Function.uncurry (Analytic.sequenceFamily
        (fun b => exactSaddleEquation r A z j (b + N)) (limitingEquation r A z j)))
        (ball ζ δ ×ˢ univ) ∧
      ∀ q : OnePoint ℕ, DifferentiableOn ℂ
        (fun s => Analytic.sequenceFamily (fun b => exactSaddleEquation r A z j (b + N))
          (limitingEquation r A z j) s q) (ball ζ δ) := by
  obtain ⟨d, hd, κ, hκ, η, hη, M, hM, hregion⟩ := exists_local_slit_region hζ
  have hslit : ball ζ d ⊆ Complex.slitPlane := fun s hs =>
    region_mem_slitPlane hκ hη (hregion s (ball_subset_closedBall hs)).2
  have hF : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (exactSaddleEquation r A z j n) (ball ζ d) := by
    filter_upwards [eventually_scaled_slit_in_kernelDomain (by omega : 0 < r) hA M] with n hn
    apply (differentiableOn_exactSaddleEquation r A z j n).mono
    intro s hs
    exact hn s ((Complex.re_le_norm s).trans (hregion s (ball_subset_closedBall hs)).1) (hslit hs)
  have hf : DifferentiableOn ℂ (limitingEquation r A z j) (ball ζ d) := fun s hs =>
    (hasDerivAt_limitingEquation r A z j (hslit hs)).differentiableAt.differentiableWithinAt
  have hsub : closedBall ζ (d / 2) ⊆ ball ζ d := closedBall_subset_ball (half_lt_self hd)
  obtain ⟨C, _, herr⟩ := uniform_exactSaddleEquation_region hr hA z j hκ hη hM
  have hlim : TendstoUniformlyOn (fun n => exactSaddleEquation r A z j n)
      (limitingEquation r A z j) atTop (closedBall ζ (d / 2)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have ht : Tendsto (fun n => C * smallParameter r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (smallParameter_tendsto (show 0 < r by omega)).const_mul C
    filter_upwards [herr, ht.eventually_lt_const hε] with n hn hsmall s hs
    have hg := hregion s (ball_subset_closedBall (hsub hs))
    rw [dist_eq_norm, norm_sub_rev]
    exact (hn s hg.1 hg.2).trans_lt hsmall
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hF
  refine ⟨d / 2, half_pos hd, (fun s hs => hslit (hsub (ball_subset_closedBall hs))), ?_⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hhol (b : ℕ) := hN₀ (b + N) (hN.trans (Nat.le_add_left N b))
  have hcont := Analytic.continuousOn_sequenceFamily (isCompact_closedBall ζ (d / 2))
    (fun b => ((hhol b).mono hsub).continuousOn) ((hf.mono hsub).continuousOn)
    (hlim.seq_tendstoUniformlyOn (fun b => b + N) (tendsto_add_atTop_nat N))
  refine ⟨hcont.mono (Set.prod_mono ball_subset_closedBall Subset.rfl), ?_⟩
  intro q
  cases q with
  | infty => exact hf.mono (fun _ hs => hsub (ball_subset_closedBall hs))
  | coe b => exact (hhol b).mono (fun _ hs => hsub (ball_subset_closedBall hs))

end ThisWork.HigherRank
