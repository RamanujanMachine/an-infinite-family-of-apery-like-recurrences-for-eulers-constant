module

public import Neuschel.PhaseFactor

/-! Parameter-uniform Taylor expansions with analytic remainders. -/

public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

theorem phaseQuotient_step {Z : Type*} (n : ℕ) (a t : ℂ) (p : ℂ → Z → ℂ) (z : Z) :
    (t - a) * phaseQuotient (n + 1) a p t z = phaseQuotient n a p t z - phaseQuotient n a p a z := by
  simpa only [phaseQuotient, Function.iterate_succ_apply', Function.swap, smul_eq_mul] using
    sub_smul_dslope (fun u => phaseQuotient n a p u z) a t

theorem eq_taylor_add_remainder {Z : Type*} (m : ℕ) (a t : ℂ) (p : ℂ → Z → ℂ) (z : Z) :
    p t z = (∑ n ∈ Finset.range m, phaseQuotient n a p a z * (t - a) ^ n) +
      (t - a) ^ m * phaseQuotient m a p t z := by
  induction m with
  | zero => simp [phaseQuotient]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    linear_combination -(t - a) ^ m * phaseQuotient_step m a t p z

/-- A single Taylor remainder constant works for every parameter on each smaller
closed disk. The proof uses the analytic quotient, rather than pointwise radii. -/
theorem uniform_taylor_remainder {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (m : ℕ) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G)
    {r : ℝ} (hrG : closedBall a r ⊆ G) :
    ∃ M ≥ 0, ∀ t ∈ closedBall a r, ∀ z,
      ‖p t z - ∑ n ∈ Finset.range m, phaseQuotient n a p a z * (t - a) ^ n‖ ≤
        M * ‖t - a‖ ^ m := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall a r |>.prod (isCompact_univ (X := Z))).exists_bound_of_continuousOn
    ((phaseQuotient_regular m hG ha hp hd).1.mono (Set.prod_mono hrG Subset.rfl))
  refine ⟨max C 0, le_max_right _ _, fun t ht z => ?_⟩
  rw [eq_taylor_add_remainder m a t p z, add_sub_cancel_left, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left ((hC (t, z) ⟨ht, mem_univ z⟩).trans (le_max_left C 0))
    (pow_nonneg (norm_nonneg _) m)).trans_eq (mul_comm _ _)

end Neuschel
