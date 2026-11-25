module

public import ThisWork.CompactFamilyTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric MeasureTheory
open scoped Topology OnePoint

theorem hasDerivAt_segmentIntegral_ball {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball 0 r)) {s : ℂ} (hs : s ∈ ball 0 r) :
    HasDerivAt (fun t => Neuschel.segmentIntegral F 0 t) (F s) s := by
  obtain ⟨g, hg0, hg⟩ := hF.isExactOn_ball.with_val_at 0 0
  have he : (fun t => Neuschel.segmentIntegral F 0 t) =ᶠ[𝓝 s] g :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hs) (fun t ht => by
      simpa only [Set.mem_ofPred_eq, hg0, sub_zero] using
        Neuschel.segmentIntegral_eq_primitive_sub (convex_ball 0 r) hg hF.continuousOn (mem_ball_self hr) ht)
  exact (hg s hs).congr_of_eventuallyEq he

theorem continuousOn_segmentIntegral_family {Z : Type*} [TopologicalSpace Z]
    {Q : ℂ → Z → ℂ} {r : ℝ}
    (hQ : ContinuousOn (Function.uncurry Q) (ball 0 r ×ˢ univ)) :
    ContinuousOn (Function.uncurry (fun t z => Neuschel.segmentIntegral (fun u => Q u z) 0 t))
      (ball 0 r ×ˢ univ) := by
  let T := (ball (0 : ℂ) r) × Z
  let clamp (u : ℝ) := max 0 (min 1 u)
  have hclamp (u : ℝ) : 0 ≤ clamp u ∧ clamp u ≤ 1 :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hmap (w : T × ℝ) : (((clamp w.2 : ℝ) : ℂ) * w.1.1.val, w.1.2) ∈
      ball (0 : ℂ) r ×ˢ univ := by
    refine ⟨?_, mem_univ _⟩
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_of_nonneg (hclamp w.2).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hclamp w.2).2).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using w.1.1.property)
  have hc : Continuous (fun w : T × ℝ => Q (((clamp w.2 : ℝ) : ℂ) * w.1.1.val) w.1.2) :=
    hQ.comp_continuous (by dsimp only [T, clamp]; fun_prop) hmap
  have hi : Continuous (fun x : T => ∫ u : ℝ in 0..1,
      x.1.val * Q (((clamp u : ℝ) : ℂ) * x.1.val) x.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul hc) 0 1
  rw [continuousOn_iff_continuous_domRestrict]
  have hin : Continuous (fun w : (ball (0 : ℂ) r ×ˢ (univ : Set Z)) =>
      ((⟨w.val.1, w.property.1⟩ : ball (0 : ℂ) r), w.val.2)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (continuous_snd.comp continuous_subtype_val)
  convert hi.comp hin using 1
  funext w
  change (∫ u : ℝ in 0..1, (w.val.1 - 0) * Q (AffineMap.lineMap 0 w.val.1 u) w.val.2) = _
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : 0 ≤ u ∧ u ≤ 1 := by simpa only [uIcc_of_le zero_le_one, mem_Icc] using hu
  simp only [clamp, min_eq_right hu'.2, max_eq_right hu'.1, AffineMap.lineMap_apply_module,
    smul_zero, zero_add, sub_zero, Complex.real_smul]

theorem eq_neg_segmentIntegral_of_derivative {p Q : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hQ : DifferentiableOn ℂ Q (ball 0 r)) (hp0 : p 0 = 0)
    (hp : ∀ t ∈ ball 0 r, HasDerivAt p (-Q t) t) :
    EqOn p (fun t => -Neuschel.segmentIntegral Q 0 t) (ball 0 r) := by
  apply isOpen_ball.eqOn_of_deriv_eq (convex_ball 0 r).isPreconnected
    (fun t ht => (hp t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hasDerivAt_segmentIntegral_ball hr hQ ht).neg.differentiableAt.differentiableWithinAt)
    (fun t ht => (hp t ht).deriv.trans ((hasDerivAt_segmentIntegral_ball hr hQ ht).neg.deriv).symm)
    (mem_ball_self hr)
  simp only [hp0, Neuschel.segmentIntegral, sub_self, zero_mul, intervalIntegral.integral_zero,
    Pi.neg_apply, neg_zero]

end ThisWork.Analytic
