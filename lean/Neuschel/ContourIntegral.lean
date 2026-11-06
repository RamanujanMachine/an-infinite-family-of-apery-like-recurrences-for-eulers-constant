module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-! Contour integration and straightening inside a holomorphic coordinate disk. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

/-- The real-parameter chain rule for a complex holomorphic primitive. -/
theorem hasDerivAt_primitive_comp {F f : ℂ → ℂ} {γ : ℝ → ℂ} {v : ℂ} {s : ℝ}
    (hF : HasDerivAt F (f (γ s)) (γ s)) (hγ : HasDerivAt γ v s) :
    HasDerivAt (fun u => F (γ u)) (v * f (γ s)) s := by
  simpa [smul_eq_mul, Function.comp_def] using
    ((hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hγ)

/-- Fundamental theorem for a parametrized contour with a holomorphic primitive.
Endpoint derivatives are unnecessary. -/
theorem contour_integral_eq_primitive_sub {A B : ℝ} (hAB : A ≤ B) {U : Set ℂ}
    {F f : ℂ → ℂ} (hF : ∀ t ∈ U, HasDerivAt F (f t) t)
    {γ v : ℝ → ℂ} (hc : ContinuousOn γ (Icc A B))
    (hd : ∀ s ∈ Ioo A B, HasDerivAt γ (v s) s) (hU : MapsTo γ (Icc A B) U)
    (hi : IntervalIntegrable (fun s => v s * f (γ s)) volume A B) :
    ∫ s in A..B, v s * f (γ s) = F (γ B) - F (γ A) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hAB
    (fun s hs => (hF (γ s) (hU hs)).continuousAt.comp_continuousWithinAt (hc s hs))
    (fun s hs => hasDerivAt_primitive_comp (hF (γ s) (hU (Ioo_subset_Icc_self hs))) (hd s hs)) hi

@[expose] noncomputable def segmentIntegral (f : ℂ → ℂ) (x y : ℂ) : ℂ :=
  ∫ s : ℝ in 0..1, (y - x) * f (AffineMap.lineMap x y s)

theorem segment_integrable {U : Set ℂ} (hconv : Convex ℝ U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    IntervalIntegrable (fun t : ℝ => (y - x) * f (AffineMap.lineMap x y t)) volume 0 1 :=
  (continuousOn_const.mul (hf.comp AffineMap.lineMap_continuous.continuousOn
    (hconv.mapsTo_lineMap hx hy))).intervalIntegrable_of_Icc zero_le_one

theorem segmentIntegral_sub {U : Set ℂ} (hconv : Convex ℝ U) {f g : ℂ → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    segmentIntegral (fun w => f w - g w) x y = segmentIntegral f x y - segmentIntegral g x y := by
  simpa only [segmentIntegral, mul_sub] using
    intervalIntegral.integral_sub (segment_integrable hconv hf hx hy) (segment_integrable hconv hg hx hy)

theorem segmentIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (x y : ℂ) :
    segmentIntegral (fun w => c * f w) x y = c * segmentIntegral f x y := by
  simp only [segmentIntegral, mul_left_comm (y - x) c, intervalIntegral.integral_const_mul]

theorem segmentIntegral_finsetSum {ι : Type*} (S : Finset ι) {U : Set ℂ}
    (hconv : Convex ℝ U) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, ContinuousOn (f i) U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    segmentIntegral (fun w => ∑ i ∈ S, f i w) x y = ∑ i ∈ S, segmentIntegral (f i) x y := by
  simpa only [segmentIntegral, Finset.mul_sum] using
    intervalIntegral.integral_finsetSum (fun i hi => segment_integrable hconv (hf i hi) hx hy)

theorem segmentIntegral_congr_ball {f g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hfg : EqOn f g (ball c r)) {x y : ℂ} (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    segmentIntegral f x y = segmentIntegral g x y :=
  intervalIntegral.integral_congr (fun s hs => congrArg (fun u : ℂ => (y - x) * u)
    (hfg ((convex_ball c r).lineMap_mem hx hy (by simpa only [uIcc_of_le zero_le_one] using hs))))

theorem segmentIntegral_eq_primitive_sub {U : Set ℂ} (hconv : Convex ℝ U)
    {F f : ℂ → ℂ} (hF : ∀ t ∈ U, HasDerivAt F (f t) t) (hf : ContinuousOn f U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    segmentIntegral f x y = F y - F x := by
  have hmap := hconv.mapsTo_lineMap hx hy
  simpa only [segmentIntegral, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    contour_integral_eq_primitive_sub zero_le_one hF AffineMap.lineMap_continuous.continuousOn
      (fun _ _ => AffineMap.hasDerivAt_lineMap) hmap
      ((continuousOn_const.mul (hf.comp AffineMap.lineMap_continuous.continuousOn hmap)).intervalIntegrable_of_Icc
        zero_le_one)

/-- A contour inside a holomorphic disk may be straightened to the segment
between its endpoints. This follows from a primitive on the entire disk. -/
theorem contour_integral_eq_segment {A B : ℝ} (hAB : A ≤ B) {c : ℂ} {r : ℝ}
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c r)) {γ v : ℝ → ℂ}
    (hc : ContinuousOn γ (Icc A B)) (hv : ContinuousOn v (Icc A B))
    (hd : ∀ s ∈ Ioo A B, HasDerivAt γ (v s) s)
    (hmap : MapsTo γ (Icc A B) (ball c r)) :
    ∫ s in A..B, v s * f (γ s) = segmentIntegral f (γ A) (γ B) := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  exact (contour_integral_eq_primitive_sub hAB hF hc hd hmap
    ((hv.mul (hf.continuousOn.comp hc hmap)).intervalIntegrable_of_Icc hAB)).trans
      (segmentIntegral_eq_primitive_sub (convex_ball c r) hF hf.continuousOn
        (hmap (left_mem_Icc.mpr hAB)) (hmap (right_mem_Icc.mpr hAB))).symm

end Neuschel
