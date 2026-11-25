module

public import ThisWork.BoundaryMomentConvergence

/-! The fixed finite pieces of each weighted boundary contour are polynomial
relative to the common Gamma scale. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

theorem fixedPolynomialBound_weighted_boundary_path {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (k : ℕ)
    {γ : ℝ → ℂ} {a b : ℝ} (hc : ContinuousOn γ (uIcc a b))
    (hslit : ∀ u ∈ uIcc a b, γ u ∈ Complex.slitPlane)
    (hleft : ∀ u ∈ uIcc a b, (γ u).re < 1) (w : ℂ) :
    FixedPolynomialBound (commonScale r 0 A z)
      (fun n => ∫ u in a..b, w * ((-γ u) ^ k * boundaryKernel r 0 A z n (γ u))) := by
  let K := γ '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨B, hB, C, hC, hb⟩ := uniform_boundaryKernel_fixed_compact_bound hr hA hz 0 hK
    (by rintro x ⟨u, hu, rfl⟩; exact hslit u hu)
    (by rintro x ⟨u, hu, rfl⟩; exact hleft u hu)
  apply fixedPolynomialBound_integral (K := K)
    (f := fun n x => (-x) ^ k * boundaryKernel r 0 A z n x)
    (fun u hu => ⟨u, hu, rfl⟩) w
  refine ⟨max 0 M ^ k * B, by positivity, C, hC, ?_⟩
  filter_upwards [hb] with n hn x hx
  rw [norm_mul, norm_pow, norm_neg]
  have hp := pow_le_pow_left₀ (norm_nonneg x) ((hM x hx).trans (le_max_right 0 M)) k
  exact (mul_le_mul hp (hn x hx) (norm_nonneg _) (by positivity)).trans_eq (by ring)

noncomputable def boundaryFiniteMoment (r : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (n k : ℕ) (L : ℝ) : ℂ :=
  (∫ u in L..(1 / 2 : ℝ), (-((u : ℂ) - Complex.I)) ^ k *
    boundaryKernel r 0 A z n ((u : ℂ) - Complex.I)) -
  (∫ u in L..(1 / 2 : ℝ), (-((u : ℂ) + Complex.I)) ^ k *
    boundaryKernel r 0 A z n ((u : ℂ) + Complex.I)) +
  (∫ y in (-1 : ℝ)..1, Complex.I *
    ((-((1 / 2 : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      boundaryKernel r 0 A z n ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)))

theorem boundaryFiniteMoment_polynomial_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z L : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (k : ℕ) (hL : L ≤ 1 / 2) :
    FixedPolynomialBound (commonScale r 0 A z) (fun n => boundaryFiniteMoment r A z n k L) := by
  have hlo := fixedPolynomialBound_weighted_boundary_path hr hA hz k
    (γ := fun u : ℝ => (u : ℂ) - Complex.I) (a := L) (b := 1 / 2) (by fun_prop)
    (fun _ _ => Complex.mem_slitPlane_iff.mpr (Or.inr (by simp)))
    (fun u hu => by rw [uIcc_of_le hL] at hu; simpa using lt_of_le_of_lt hu.2 (by norm_num : (1 / 2 : ℝ) < 1)) (1 : ℂ)
  have hhi := fixedPolynomialBound_weighted_boundary_path hr hA hz k
    (γ := fun u : ℝ => (u : ℂ) + Complex.I) (a := L) (b := 1 / 2) (by fun_prop)
    (fun _ _ => Complex.mem_slitPlane_iff.mpr (Or.inr (by simp)))
    (fun u hu => by rw [uIcc_of_le hL] at hu; simpa using lt_of_le_of_lt hu.2 (by norm_num : (1 / 2 : ℝ) < 1)) (1 : ℂ)
  have hv := fixedPolynomialBound_weighted_boundary_path hr hA hz k
    (γ := fun y : ℝ => (1 / 2 : ℂ) + (y : ℂ) * Complex.I) (a := -1) (b := 1) (by fun_prop)
    (fun _ _ => Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [Complex.mul_re])))
    (fun _ _ => by norm_num [Complex.mul_re]) Complex.I
  have hs (n : ℕ) : 0 ≤ commonScale r 0 A z n := (commonScale_pos hA hz 0 n).le
  simpa only [one_mul, boundaryFiniteMoment] using (hlo.sub hs hhi).add hs hv

end ThisWork
