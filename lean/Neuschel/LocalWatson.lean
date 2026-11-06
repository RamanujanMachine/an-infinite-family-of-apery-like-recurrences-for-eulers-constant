module

public import Neuschel.RayTaylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform Watson expansion on the straightened local ray. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

/-- Finite sums preserve a common uniform error scale. -/
theorem uniform_finset_error {ι X : Type*} (S : Finset ι) {F : ι → X → ℂ}
    {g : X → ℝ}
    (hF : ∀ i ∈ S, ∃ C ≥ 0, ∀ x, ‖F i x‖ ≤ C * g x) :
    ∃ C ≥ 0, ∀ x, ‖∑ i ∈ S, F i x‖ ≤ C * g x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨A, hA, hAi⟩ := hF i (Finset.mem_insert_self i S)
    obtain ⟨B, hB, hBS⟩ := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    refine ⟨A + B, add_nonneg hA hB, fun x => ?_⟩
    simpa only [Finset.sum_insert hi, add_mul] using
      (norm_add_le (F i x) (∑ j ∈ S, F j x)).trans (add_le_add (hAi x) (hBS x))

/-- Taylor coefficients of a jointly continuous holomorphic compact family
are uniformly bounded in the parameter. -/
theorem uniform_taylor_coefficient_bound {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (j : ℕ) {D : ℝ} (hD : 0 < D) {A : ℂ → Z → ℂ}
    (hA : ContinuousOn (Function.uncurry A) (ball (0 : ℂ) D ×ˢ univ))
    (hdA : ∀ z, DifferentiableOn ℂ (fun w => A w z) (ball 0 D)) :
    ∃ B ≥ 0, ∀ z, ‖phaseQuotient j 0 A 0 z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_singleton (x := (0 : ℂ)) |>.prod (isCompact_univ (X := Z))).exists_bound_of_continuousOn
    ((phaseQuotient_regular j isOpen_ball (mem_ball_self hD) hA hdA).1.mono
      (Set.prod_mono (singleton_subset_iff.mpr (mem_ball_self hD)) Subset.rfl))
  exact ⟨max B 0, le_max_right _ _, fun z =>
    (hB (0, z) ⟨mem_singleton 0, mem_univ z⟩).trans (le_max_left _ _)⟩

/-- The finite Taylor polynomial contributes its uniform Gamma sum, up to an
exponentially small error. -/
theorem uniform_taylor_moment_error {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (m k : ℕ) {D η : ℝ} (hD : 0 < D) (hη : 0 < η)
    {A : ℂ → Z → ℂ} (hA : ContinuousOn (Function.uncurry A) (ball (0 : ℂ) D ×ˢ univ))
    (hdA : ∀ z, DifferentiableOn ℂ (fun w => A w z) (ball 0 D))
    {α : Z → ℂ} (hα : Continuous α) (hgap : ∀ z, η ≤ (α z).re) :
    ∃ C ≥ 0, ∀ n : ℝ, 1 ≤ n → ∀ z,
      ‖∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z *
        (segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ (j + k))
          0 (normalizedRoot μ (α z)) -
          (μ : ℂ)⁻¹ * ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
            n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ))‖ ≤
        C * Real.exp (-(n - 1) * η) := by
  let X := {x : ℝ × Z // 1 ≤ x.1}
  obtain ⟨C, hC, hbound⟩ := uniform_finset_error (X := X) (Finset.range m)
    (F := fun j x => phaseQuotient j 0 A 0 x.val.2 *
      (segmentIntegral (fun w => Complex.exp (-(x.val.1 : ℂ) * w ^ μ) * w ^ (j + k))
        0 (normalizedRoot μ (α x.val.2)) -
        (μ : ℂ)⁻¹ * ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
          x.val.1 ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)))
    (g := fun x => Real.exp (-(x.val.1 - 1) * η)) (fun j _ => by
      obtain ⟨B, hB, hBj⟩ := uniform_taylor_coefficient_bound j hD hA hdA
      obtain ⟨C, hC, hCj⟩ := uniform_segment_monomial hμ (j + k) hη hα hgap
      refine ⟨B * C, mul_nonneg hB hC, fun x => ?_⟩
      simpa only [norm_mul, mul_assoc] using
        mul_le_mul (hBj x.val.2) (hCj x.val.1 x.property x.val.2) (norm_nonneg _) hB)
  exact ⟨C, hC, fun n hn z => hbound ⟨(n, z), hn⟩⟩

/-- Uniform local Watson expansion, with the algebraic and exponentially small
errors kept separate. The endpoint is the branch selected by the phase. -/
theorem uniform_local_watson_bounds {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (m k : ℕ) {r D η : ℝ} (hr : 0 ≤ r) (hrD : r < D) (hη : 0 < η)
    {A : ℂ → Z → ℂ} (hA : ContinuousOn (Function.uncurry A) (ball (0 : ℂ) D ×ˢ univ))
    (hdA : ∀ z, DifferentiableOn ℂ (fun w => A w z) (ball 0 D))
    {α : Z → ℂ} (hα : Continuous α) (hgap : ∀ z, η ≤ (α z).re)
    (hρ : ∀ z, ‖normalizedRoot μ (α z)‖ ≤ r) :
    ∃ C ≥ 0, ∃ E ≥ 0, ∀ n : ℝ, 1 ≤ n → ∀ z,
      ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k * A w z)
          0 (normalizedRoot μ (α z)) -
        ∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z * (μ : ℂ)⁻¹ *
          ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
            n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)‖ ≤
      C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) +
        E * Real.exp (-(n - 1) * η) := by
  have hrootgap : ∀ z, η ≤ (normalizedRoot μ (α z) ^ μ).re := fun z => by
    rw [normalizedRoot_pow hμ (Complex.slitPlane_ne_zero (Or.inl (hη.trans_le (hgap z))))]
    exact hgap z
  obtain ⟨C, hC, happrox⟩ := uniform_segment_taylor_approx hμ m k hr hrD hη hA hdA hρ hrootgap
  obtain ⟨E, hE, hmoment⟩ := uniform_taylor_moment_error hμ m k (hr.trans_lt hrD) hη hA hdA hα hgap
  refine ⟨C, hC, E, hE, fun n hn z => ?_⟩
  have htriangle := norm_add_le
    (segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k * A w z)
        0 (normalizedRoot μ (α z)) -
      ∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z *
        segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ (j + k))
          0 (normalizedRoot μ (α z)))
    (∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z *
      (segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ (j + k))
        0 (normalizedRoot μ (α z)) -
        (μ : ℂ)⁻¹ * ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
          n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)))
  have hb := htriangle.trans (add_le_add (happrox n (zero_lt_one.trans_le hn) z) (hmoment n hn z))
  simpa only [mul_sub, Finset.sum_sub_distrib, sub_add_sub_cancel, mul_assoc] using hb

/-- Every exponentially small uniform error is eventually bounded at any
prescribed algebraic scale. -/
theorem eventually_exp_shift_le_rpow {η : ℝ} (hη : 0 < η) (b B : ℝ) :
    ∀ᶠ n : ℝ in atTop, Real.exp (-(n - B) * η) ≤ Real.exp (B * η) * n ^ b := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hη b).bound zero_lt_one
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with n hn hn0
  have hn1 : Real.exp (-η * n) ≤ n ^ b := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul] using hn
  have heq : -(n - B) * η = B * η + -η * n := by ring
  rw [heq, Real.exp_add]
  exact mul_le_mul_of_nonneg_left hn1 (Real.exp_nonneg _)

/-- The all-orders uniform local Watson expansion. The coefficients come from
the analytic transformed amplitude, and the error has the next omitted order. -/
theorem uniform_local_watson {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (m k : ℕ) {r D η : ℝ} (hr : 0 ≤ r) (hrD : r < D) (hη : 0 < η)
    {A : ℂ → Z → ℂ} (hA : ContinuousOn (Function.uncurry A) (ball (0 : ℂ) D ×ˢ univ))
    (hdA : ∀ z, DifferentiableOn ℂ (fun w => A w z) (ball 0 D))
    {α : Z → ℂ} (hα : Continuous α) (hgap : ∀ z, η ≤ (α z).re)
    (hρ : ∀ z, ‖normalizedRoot μ (α z)‖ ≤ r) :
    ∃ C ≥ 0, ∀ᶠ n : ℝ in atTop, ∀ z,
      ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k * A w z)
          0 (normalizedRoot μ (α z)) -
        ∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z * (μ : ℂ)⁻¹ *
          ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
            n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)‖ ≤
      C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) := by
  obtain ⟨C, hC, E, hE, hb⟩ := uniform_local_watson_bounds hμ m k hr hrD hη hA hdA hα hgap hρ
  refine ⟨C + E * Real.exp η, add_nonneg hC (mul_nonneg hE (Real.exp_nonneg _)), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_exp_shift_le_rpow hη (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) 1] with n hn hexp z
  exact (hb n hn z).trans (by
    simpa only [one_mul, add_mul, mul_assoc] using
      add_le_add (le_refl (C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ)))))
        (mul_le_mul_of_nonneg_left hexp hE))

end Neuschel
