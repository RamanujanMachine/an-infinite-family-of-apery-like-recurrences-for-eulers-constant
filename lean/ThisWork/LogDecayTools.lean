module

public import ThisWork.DigammaTailTools

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork.Analytic

open Set Filter Metric
open scoped Topology

theorem log_decay_of_derivative_bound {f df : ℝ → ℝ} {R C a t : ℝ}
    (hf : ∀ u : ℝ, 1 ≤ u → HasDerivAt f (df u) u)
    (hb : ∀ u : ℝ, 1 ≤ u → df u ≤ -R * (Real.log u - C))
    (ha : 1 ≤ a) (hat : a ≤ t) :
    f t - f a ≤ -R * (t * Real.log t - a * Real.log a - (C + 1) * (t - a)) := by
  have hd (u : ℝ) (hu : 1 ≤ u) :
      HasDerivAt (fun v : ℝ => f v + R * (v * Real.log v - (C + 1) * v))
        (df u + R * (Real.log u - C)) u := by
    convert (hf u hu).add ((((hasDerivAt_id u).mul (Real.hasDerivAt_log (by linarith : u ≠ 0))).sub
      ((hasDerivAt_id u).const_mul (C + 1))).const_mul R) using 1
    · funext v
      rfl
    · simp only [id_eq, one_mul, mul_one, mul_inv_cancel₀ (show u ≠ 0 by linarith)]
      ring
  have hm : AntitoneOn (fun v : ℝ => f v + R * (v * Real.log v - (C + 1) * v)) (Ici 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
      (fun u hu => by linarith [hb u (interior_subset hu)])
  nlinarith [hm ha (ha.trans hat) hat]

end ThisWork.Analytic
