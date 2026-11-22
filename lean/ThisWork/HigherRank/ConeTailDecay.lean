module

public import ThisWork.HigherRank.ConeTailDerivative
public import ThisWork.HigherRank.IntegratedTails

/-! Exponential and integrated moment decay in the full left cone, without
an upper bound on contour height in the choice of the cutoff. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem linear_log_decay_of_derivative_bound {f df : ℝ → ℝ} {a t L : ℝ}
    (hf : ∀ u, a ≤ u → HasDerivAt f (df u) u)
    (hb : ∀ u, a ≤ u → df u ≤ -L) (hat : a ≤ t) : f t - f a ≤ -L * (t - a) := by
  exact (convex_Ici a).image_sub_le_mul_sub_of_deriv_le
    (fun u hu => (hf u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hf u (interior_subset hu)).deriv]; exact hb u (interior_subset hu))
    a le_rfl t hat hat

theorem uniform_kernel_cone_tail_decay {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η : ℝ} (hη : 0 < η)
    (m : ℕ) (z : ℝ) (j : ℤ) (q : ℝ) :
    ∃ T ≥ 1, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a → ∀ t : ℝ, a ≤ t →
      ∀ y : ℝ, η ≤ |y| → |y| ≤ a →
      ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-q * largeScale r n * (t - a)) := by
  obtain ⟨C, _, hb⟩ := uniform_re_exactSaddleEquation_cone_lower hr hA hη z j
  let T := Real.exp (C + q) + 1
  have hT : 1 ≤ T := by dsimp only [T]; linarith [Real.exp_pos (C + q)]
  refine ⟨T, hT, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℕ)] with n hn hn0 a ha t hat y hy hya
  have ha1 := hT.trans ha
  have hapos : 0 < a := zero_lt_one.trans_le ha1
  have hy0 : y ≠ 0 := by intro he; rw [he, abs_zero] at hy; linarith
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hloga : C + q ≤ Real.log a := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (C + q))
      (by dsimp only [T] at ha; linarith : Real.exp (C + q) ≤ a)
  have hd := linear_log_decay_of_derivative_bound
    (f := fun u => Real.log ‖kernel r m A z j n
      ((largeScale r n : ℂ) * (-(u : ℂ) + (y : ℂ) * Complex.I))‖)
    (L := q * largeScale r n)
    (fun u hu => hasDerivAt_log_norm_kernel_left hA m z j hn0 (hapos.trans_le hu) hy0)
    (fun u hu => by
      have h := hn u (ha1.trans hu) y hy (hya.trans hu)
      have hl := Real.log_le_log hapos hu
      nlinarith [mul_le_mul_of_nonneg_left (show q ≤
        (exactSaddleEquation r A z j n (-(u : ℂ) + (y : ℂ) * Complex.I)).re by linarith) hR.le]) hat
  have hKa : 0 < ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ :=
    norm_pos_iff.mpr (kernel_ne_zero m z j n (scaled_left_mem_kernelDomain hA n hR hapos hy0))
  calc
    _ ≤ Real.exp (Real.log ‖kernel r m A z j n
        ((largeScale r n : ℂ) * (-(t : ℂ) + (y : ℂ) * Complex.I))‖) := Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel r m A z j n
        ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ - q * largeScale r n * (t - a)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log hKa, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring

theorem uniform_integrated_cone_moment_tail {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {η : ℝ} (hη : 0 < η)
    (m : ℕ) (z : ℝ) (j : ℤ) (k : ℕ) :
    ∃ T ≥ 2, ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, T ≤ a → ∀ y : ℝ, η ≤ |y| → |y| ≤ a →
      IntegrableOn (scaledLeftMomentKernel r m A z j n k y) (Ioi a) ∧
        ‖∫ t in Ioi a, scaledLeftMomentKernel r m A z j n k y t‖ ≤
          Real.exp a * ‖kernel r m A z j n
            ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ / largeScale r n := by
  obtain ⟨T₀, hT₀, hb⟩ := uniform_kernel_cone_tail_decay hr hA hη m z j 2
  obtain ⟨Tp, hTp⟩ := eventually_atTop.mp (Analytic.eventually_shifted_pow_le_exp (D := 0) le_rfl (2 * k))
  let T := max 2 (max T₀ Tp)
  have hTT : T₀ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTP : Tp ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, le_max_left _ _, ?_⟩
  filter_upwards [hb, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (1 : ℝ))] with n hn hR a ha y hy hya
  have hR0 : 0 < largeScale r n := zero_lt_one.trans_le hR
  have hy0 : y ≠ 0 := by intro he; rw [he, abs_zero] at hy; linarith
  have ha2 : 2 ≤ a := (le_max_left _ _).trans ha
  have hcont : ContinuousOn (scaledLeftMomentKernel r m A z j n k y) (Ioi a) := by
    apply ContinuousOn.mul (by fun_prop)
    exact (show ContinuousOn (kernel r m A z j n) (kernelDomain r A n) from
      (show DifferentiableOn ℂ (kernel r m A z j n) (kernelDomain r A n) from
        fun _ hs => (differentiableAt_kernel m z j n hs).differentiableWithinAt).continuousOn).comp
      (by fun_prop) (fun t ht => scaled_left_mem_kernelDomain hA n hR0 (by
        have ht' : a < t := ht
        linarith) hy0)
  apply integral_norm_le_shifted_exp_tail hR0 (hcont.aestronglyMeasurable measurableSet_Ioi)
  intro t ht
  have hat : a ≤ t := ht.le
  have ht2 : 2 ≤ t := ha2.trans hat
  have hpoly : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ^ k ≤ Real.exp t := by
    have hs : ‖-(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ 2 * t := by
      simpa only [Nat.cast_zero, zero_sub, norm_neg, zero_add, ← two_mul] using
        Analytic.norm_polynomial_left_le (by linarith : 0 ≤ t) (hya.trans hat) 0
    calc
      _ ≤ (t ^ 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) (hs.trans (by nlinarith)) k
      _ = t ^ (2 * k) := (pow_mul t 2 k).symm
      _ ≤ _ := by simpa only [add_zero] using hTp t (hTP.trans (ha.trans hat))
  have hkernel := hn a (hTT.trans ha) t hat y hy hya
  rw [scaledLeftMomentKernel, norm_mul, norm_pow]
  calc
    _ ≤ Real.exp t * (‖kernel r m A z j n
        ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
          Real.exp (-2 * largeScale r n * (t - a))) :=
      mul_le_mul hpoly hkernel (norm_nonneg _) (Real.exp_pos t).le
    _ = ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
        Real.exp (t - 2 * largeScale r n * (t - a)) := by
          rw [show t - 2 * largeScale r n * (t - a) = t + (-2 * largeScale r n * (t - a)) by ring,
            Real.exp_add]
          ring
    _ ≤ ‖kernel r m A z j n ((largeScale r n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ *
        Real.exp (a - largeScale r n * (t - a)) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hat)])) (norm_nonneg _)
    _ = _ := by
      rw [show a - largeScale r n * (t - a) = a + (-largeScale r n * (t - a)) by ring, Real.exp_add]
      ring

end ThisWork.HigherRank
