module

public import ThisWork.CompactSaddles
public import ThisWork.PrimitiveTools

/-! Canonical centered primitives for the compact arbitrary-rank saddle
families. The original parameter-family integration machinery is reused. -/

@[expose] public section
namespace ThisWork.CompactSaddleFamily

open Set Filter Metric
open scoped Topology OnePoint

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}
    (S : CompactSaddleFamily r A z j ζ δ)

noncomputable def phase (t : ℂ) (q : OnePoint ℕ) : ℂ :=
  -Neuschel.segmentIntegral (fun u => S.shiftedEquation u q) 0 t

theorem continuous_phase : ContinuousOn (Function.uncurry S.phase) (ball 0 (δ / 2) ×ˢ univ) :=
  (Analytic.continuousOn_segmentIntegral_family S.continuous_shiftedEquation).neg

theorem hasDerivAt_phase {t : ℂ} (ht : t ∈ ball 0 (δ / 2)) (q : OnePoint ℕ) :
    HasDerivAt (fun u => S.phase u q) (-S.shiftedEquation t q) t :=
  (Analytic.hasDerivAt_segmentIntegral_ball (half_pos S.radius_pos)
    (S.differentiableOn_shiftedEquation q) ht).neg

@[simp] theorem phase_zero (q : OnePoint ℕ) : S.phase 0 q = 0 := by
  simp only [phase, Neuschel.segmentIntegral, sub_self, zero_mul, intervalIntegral.integral_zero, neg_zero]

theorem differentiableOn_phase (q : OnePoint ℕ) :
    DifferentiableOn ℂ (fun t => S.phase t q) (ball 0 (δ / 2)) :=
  fun _ ht => (S.hasDerivAt_phase ht q).differentiableAt.differentiableWithinAt

theorem phase_simple_saddle (q : OnePoint ℕ) :
    deriv (fun t => S.phase t q) 0 = 0 ∧ deriv (deriv (fun t => S.phase t q)) 0 ≠ 0 :=
  Analytic.phase_simple_saddle (mem_ball_self (half_pos S.radius_pos))
    (fun _ ht => S.hasDerivAt_phase ht q) (S.shiftedEquation_zero q) (S.shiftedEquation_simple q)

theorem phase_limit (hslit : ball ζ δ ⊆ Complex.slitPlane) {t : ℂ} (ht : t ∈ ball 0 (δ / 2)) :
    S.phase t ∞ = limitingPhase r A z j ζ - limitingPhase r A z j (t + ζ) := by
  have hd : ∀ u ∈ ball 0 (δ / 2),
      HasDerivAt (fun v => limitingPhase r A z j (v + ζ)) (S.shiftedEquation u ∞) u := by
    intro u hu
    have hmem : u + ζ ∈ ball ζ δ := by simpa only [S.saddle_limit] using S.shifted_mem hu ∞
    simpa only [S.shiftedEquation_limit, Function.comp_def, id_eq, mul_one] using
      (hasDerivAt_limitingPhase r A z j (hslit hmem)).comp u ((hasDerivAt_id u).add_const ζ)
  have he := Neuschel.segmentIntegral_eq_primitive_sub (convex_ball 0 (δ / 2)) hd
    (S.differentiableOn_shiftedEquation ∞).continuousOn
    (mem_ball_self (half_pos S.radius_pos)) ht
  simpa only [phase, zero_add, neg_sub] using congrArg Neg.neg he

theorem eventually_kernel_eq_phase (hr : 0 < r) (hA : ∀ i, 0 < A i)
    (hslit : ball ζ δ ⊆ Complex.slitPlane) (b : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ t ∈ ball 0 (δ / 2),
      kernel r b A z j (k + S.firstIndex)
        ((largeScale r (k + S.firstIndex) : ℂ) * (t + S.saddle k)) =
      kernel r b A z j (k + S.firstIndex)
        ((largeScale r (k + S.firstIndex) : ℂ) * S.saddle k) *
          Complex.exp (-(largeScale r (k + S.firstIndex) : ℂ) * S.phase t k) := by
  filter_upwards [(tendsto_add_atTop_nat S.firstIndex).eventually
    (eventually_scaled_slit_in_kernelDomain hr hA (‖ζ‖ + δ)),
    (tendsto_add_atTop_nat S.firstIndex).eventually (eventually_gt_atTop (0 : ℕ))] with k hn hn0
  have hmap : MapsTo (fun s : ℂ => (largeScale r (k + S.firstIndex) : ℂ) * s)
      (ball ζ δ) (kernelDomain r A (k + S.firstIndex)) := by
    intro s hs
    have hd : ‖s - ζ‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hs
    exact hn s (by linarith [Complex.re_le_norm s, norm_sub_norm_le s ζ]) (hslit hs)
  have ha : S.saddle k ∈ ball ζ δ :=
    ball_subset_ball (by linarith [S.radius_pos] : δ / 4 ≤ δ) (S.saddle_mem k)
  obtain ⟨p, hp0, hp, hk⟩ := exists_scaled_kernel_phase b z j hn0 ha hmap
  have hcomp : ∀ t ∈ ball 0 (δ / 2),
      HasDerivAt (fun u => p (u + S.saddle k)) (-S.shiftedEquation t k) t := by
    intro t ht
    simpa only [shiftedEquation, parameterEquation, Analytic.sequenceFamily_nat,
      Function.comp_def, id_eq, mul_one] using
      (hp _ (S.shifted_mem ht k)).comp t ((hasDerivAt_id t).add_const (S.saddle k))
  have he := Analytic.eq_neg_segmentIntegral_of_derivative (half_pos S.radius_pos)
    (S.differentiableOn_shiftedEquation k) (by simpa only [zero_add] using hp0) hcomp
  intro t ht
  simpa only [phase, he ht] using hk _ (S.shifted_mem ht k)

end ThisWork.CompactSaddleFamily
