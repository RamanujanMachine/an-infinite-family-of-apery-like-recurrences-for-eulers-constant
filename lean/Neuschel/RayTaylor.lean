module

public import Neuschel.RayRemainder

/-! Exact Taylor decomposition of the straightened local Laplace integral. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

theorem weighted_polynomial (S : Finset ℕ) (d : ℕ → ℂ) (k : ℕ) (E w : ℂ) :
    (∑ j ∈ S, d j * (E * w ^ (j + k))) = E * w ^ k * ∑ j ∈ S, d j * w ^ j := by
  simp [Finset.mul_sum, pow_add, mul_comm, mul_left_comm, mul_assoc]

/-- The finite Taylor contribution and the actual remainder split exactly
under the contour integral. -/
theorem segment_taylor_decomposition (μ m k : ℕ) (κ : ℂ) {D : ℝ} (hD : 0 < D)
    {A : ℂ → ℂ} (hA : ContinuousOn A (ball (0 : ℂ) D)) (d : ℕ → ℂ)
    {ρ : ℂ} (hρ : ρ ∈ ball 0 D) :
    segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ k * A w) 0 ρ -
      (∑ j ∈ Finset.range m, d j * segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ (j + k)) 0 ρ) =
      segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * w ^ k *
        (A w - ∑ j ∈ Finset.range m, d j * w ^ j)) 0 ρ := by
  have hbase : Continuous (fun w : ℂ => Complex.exp (-κ * w ^ μ) * w ^ k) := by fun_prop
  have hpol : ∀ j : ℕ, Continuous (fun w : ℂ => d j * (Complex.exp (-κ * w ^ μ) * w ^ (j + k))) :=
    fun _ => by fun_prop
  have hsum := segmentIntegral_finsetSum (Finset.range m) (convex_ball (0 : ℂ) D)
    (fun j _ => (hpol j).continuousOn) (mem_ball_self hD) hρ
  have hsub := segmentIntegral_sub (f := fun w => Complex.exp (-κ * w ^ μ) * w ^ k * A w)
    (convex_ball (0 : ℂ) D) (hbase.continuousOn.mul hA)
    ((show Continuous (fun w : ℂ => ∑ j ∈ Finset.range m,
      d j * (Complex.exp (-κ * w ^ μ) * w ^ (j + k))) by fun_prop).continuousOn)
    (mem_ball_self hD) hρ
  have heq : (fun w => Complex.exp (-κ * w ^ μ) * w ^ k * A w -
      ∑ j ∈ Finset.range m, d j * (Complex.exp (-κ * w ^ μ) * w ^ (j + k))) =
      (fun w => Complex.exp (-κ * w ^ μ) * w ^ k * (A w - ∑ j ∈ Finset.range m, d j * w ^ j)) := by
    funext w
    rw [weighted_polynomial, mul_sub]
  simpa only [heq, hsum, segmentIntegral_const_mul] using hsub.symm

/-- Uniform approximation of the full straightened integral by its finite
Taylor-monomial contribution. -/
theorem uniform_segment_taylor_approx {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {μ : ℕ} (hμ : μ ≠ 0) (m k : ℕ) {r D η : ℝ} (hr : 0 ≤ r) (hrD : r < D) (hη : 0 < η)
    {A : ℂ → Z → ℂ} (hA : ContinuousOn (Function.uncurry A) (ball (0 : ℂ) D ×ˢ univ))
    (hdA : ∀ z, DifferentiableOn ℂ (fun w => A w z) (ball 0 D))
    {ρ : Z → ℂ} (hρ : ∀ z, ‖ρ z‖ ≤ r) (hgap : ∀ z, η ≤ (ρ z ^ μ).re) :
    ∃ C ≥ 0, ∀ n : ℝ, 0 < n → ∀ z,
      ‖segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ k * A w z) 0 (ρ z) -
        (∑ j ∈ Finset.range m, phaseQuotient j 0 A 0 z *
          segmentIntegral (fun w => Complex.exp (-(n : ℂ) * w ^ μ) * w ^ (j + k)) 0 (ρ z))‖ ≤
        C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := uniform_taylor_ray_remainder hμ m k hr hrD hη hA hdA hρ hgap
  refine ⟨C, hC0, fun n hn z => ?_⟩
  have hAz : ContinuousOn (fun w => A w z) (ball (0 : ℂ) D) :=
    hA.comp (continuousOn_id.prodMk continuousOn_const) (fun w hw => ⟨hw, mem_univ z⟩)
  rw [segment_taylor_decomposition μ m k (n : ℂ) (hr.trans_lt hrD) hAz _
    (show ρ z ∈ ball (0 : ℂ) D from by
      simpa only [mem_ball, dist_zero_right] using (hρ z).trans_lt hrD)]
  exact hC n hn z

end Neuschel
