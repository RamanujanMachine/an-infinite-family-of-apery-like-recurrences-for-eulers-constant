module

public import Neuschel.Amplitude
public import Neuschel.ContourIntegral

/-! Analytic change of variable and straightening of a local contour. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

variable {Z : Type*} [TopologicalSpace Z]
variable {p : ℂ → Z → ℂ} {a : ℂ} {G : Set ℂ}

theorem LocalInverseFamily.deriv_mul_amplitude (e : LocalInverseFamily p a G)
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) (ball a e.sourceRadius))
    (q : ℂ → Z → ℂ) {t : ℂ} {z : Z} (ht : t ∈ e.source z) :
    deriv (fun u => p u z) t * e.amplitude q (p t z) z = q t z := by
  rw [LocalInverseFamily.amplitude, (e.hasDerivAt_inverse_on_source hd ht.2 z).deriv,
    e.left_inv z t ht.1 ht.2]
  simpa only [mul_comm (q t z)] using mul_inv_cancel_left₀ (e.deriv_ne_zero t ht.1 z) (q t z)

/-- Change variables using the inverse family, then straighten the image contour
inside the common target disk. -/
theorem LocalInverseFamily.contour_substitution (e : LocalInverseFamily p a G)
    (hdp : ∀ z, DifferentiableOn ℂ (fun t => p t z) (ball a e.sourceRadius))
    {q : ℂ → Z → ℂ} (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G)
    {A B : ℝ} (hAB : A ≤ B) {γ v : ℝ → ℂ} (hc : ContinuousOn γ (Icc A B))
    (hv : ContinuousOn v (Icc A B)) (hd : ∀ s ∈ Ioo A B, HasDerivAt γ (v s) s)
    (z : Z) (hmap : MapsTo γ (Icc A B) (e.source z)) :
    ∫ s in A..B, v s * q (γ s) z =
      segmentIntegral (fun w => e.amplitude q w z) (p (γ A) z) (p (γ B) z) := by
  have hc' : ContinuousOn (fun s => p (γ s) z) (Icc A B) :=
    (hdp z).continuousOn.comp hc (fun s hs => (hmap hs).1)
  have hv' : ContinuousOn (fun s => v s * deriv (fun t => p t z) (γ s)) (Icc A B) :=
    hv.mul (((hdp z).deriv isOpen_ball).continuousOn.comp hc (fun s hs => (hmap hs).1))
  have hstraight := contour_integral_eq_segment hAB (e.differentiableOn_amplitude hdq z) hc' hv'
    (fun s hs => hasDerivAt_primitive_comp
      (((hdp z).differentiableAt (isOpen_ball.mem_nhds (hmap (Ioo_subset_Icc_self hs)).1)).hasDerivAt)
      (hd s hs)) (fun s hs => (hmap hs).2)
  refine Eq.trans (intervalIntegral.integral_congr ?_) hstraight
  intro s hs
  simpa only [mul_assoc] using congrArg (fun u : ℂ => v s * u)
    (e.deriv_mul_amplitude hdp q (hmap (by simpa only [uIcc_of_le hAB] using hs))).symm

/-- The exact local integral identity used before taking Laplace asymptotics.
The phase becomes `w^μ`; the amplitude includes the inverse Jacobian. -/
theorem LocalInverseFamily.laplace_contour_substitution (e : LocalInverseFamily p a G)
    (κ : ℂ) (μ : ℕ) {P q : ℂ → Z → ℂ}
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G)
    (hphase : ∀ w ∈ ball 0 e.targetRadius, ∀ z, P (e.inverse w z) z - P a z = w ^ μ)
    {A B : ℝ} (hAB : A ≤ B) {γ v : ℝ → ℂ} (hc : ContinuousOn γ (Icc A B))
    (hv : ContinuousOn v (Icc A B)) (hd : ∀ s ∈ Ioo A B, HasDerivAt γ (v s) s)
    (z : Z) (hmap : MapsTo γ (Icc A B) (e.source z)) :
    ∫ s in A..B, v s * (Complex.exp (-κ * (P (γ s) z - P a z)) * q (γ s) z) =
      segmentIntegral (fun w => Complex.exp (-κ * w ^ μ) * e.amplitude q w z)
        (p (γ A) z) (p (γ B) z) := by
  have hQ : ∀ z, DifferentiableOn ℂ
      (fun t => Complex.exp (-κ * (P t z - P a z)) * q t z) G :=
    fun z => ((((hdP z).sub_const _).const_mul (-κ)).cexp).mul (hdq z)
  refine (e.contour_substitution e.differentiableOn_sourceBall hQ hAB hc hv hd z hmap).trans
    (segmentIntegral_congr_ball ?_ (hmap (left_mem_Icc.mpr hAB)).2 (hmap (right_mem_Icc.mpr hAB)).2)
  intro w hw
  simp only [LocalInverseFamily.amplitude, hphase w hw z, mul_assoc]

end Neuschel
