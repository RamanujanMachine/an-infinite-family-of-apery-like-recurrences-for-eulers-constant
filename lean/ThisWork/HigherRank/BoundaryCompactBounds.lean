module

public import ThisWork.HigherRank.FixedCompactBounds
public import ThisWork.HigherRank.BoundaryReflectionBounds

/-! Bounds on the fixed finite pieces of the boundary Hankel contour. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology

theorem differentiableAt_boundaryKernel_of_slit {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hs : x ∈ Complex.slitPlane) (hx : x.re < 1) :
    DifferentiableAt ℂ (boundaryKernel r m A z n) x := by
  have hpos : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hlow := ((Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt.comp x
    (show DifferentiableAt ℂ (fun t : ℂ => 1 - t) x by fun_prop)).inv
    (Complex.Gamma_ne_zero_of_re_pos hpos)
  have hupper : DifferentiableAt ℂ (fun t : ℂ => ∏ i, Complex.Gamma ((A i : ℂ) * n - t + 1)) x :=
    DifferentiableAt.fun_finsetProd (fun i _ =>
      (Complex.hasDerivAt_Gamma_of_re_pos (upper_re_pos_of_re_lt_one hA n hx i)).differentiableAt.comp x
        (show DifferentiableAt ℂ (fun t : ℂ => (A i : ℂ) * n - t + 1) x by fun_prop))
  exact (((Complex.differentiableAt_Gamma x (Analytic.not_neg_nat_of_mem_slitPlane hs)).mul
    (hlow.pow (r - 1))).mul hupper).mul (by fun_prop) |>.mul (by fun_prop)

theorem uniform_boundaryKernel_fixed_compact_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hslit : ∀ x ∈ K, x ∈ Complex.slitPlane)
    (hleft : ∀ x ∈ K, x.re < 1) :
    ∃ B ≥ 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ K,
      ‖boundaryKernel r m A z n x‖ ≤ B * commonScale r m A z n *
        Real.exp (C * (1 + Real.log (n : ℝ))) := by
  let w : ℂ → ℂ := fun x => Complex.Gamma x * (Complex.Gamma (1 - x))⁻¹ ^ (r - 1) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * x)
  have hc : ContinuousOn w K := by
    intro x hx
    have hpos : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hleft x hx]
    have hd := ((Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt.comp x
      (show DifferentiableAt ℂ (fun t : ℂ => 1 - t) x by fun_prop)).inv (Complex.Gamma_ne_zero_of_re_pos hpos)
    exact (((Complex.differentiableAt_Gamma x (Analytic.not_neg_nat_of_mem_slitPlane (hslit x hx))).mul
      (hd.pow (r - 1))).mul (show DifferentiableAt ℂ
        (fun t : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * t)) x by fun_prop)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  obtain ⟨C, hC, hb⟩ := uniform_upperGamma_weighted_fixed_bound hr hA hz
    (le_max_left 0 M) (le_max_left 0 B) m
  refine ⟨max 0 B * Real.exp (|Real.log z| * max 0 M), by positivity, C, hC, ?_⟩
  filter_upwards [hb] with n hn x hx
  have he : boundaryKernel r m A z n x = w x *
      (∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)) *
        Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - x)) := by
    dsimp only [boundaryKernel, w]; ring
  rw [he]
  exact hn x ((hM x hx).trans (le_max_right 0 M)) _ ((hB x hx).trans (le_max_right 0 B))

end ThisWork.HigherRank
