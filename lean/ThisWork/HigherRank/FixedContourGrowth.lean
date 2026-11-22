module

public import ThisWork.HigherRank.BoundaryIntegralComparison

/-! Finite contour pieces have polynomial growth relative to the common
Gamma scale. The bounds are closed under the required finite arithmetic. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

def FixedPolynomialBound (scale : ℕ → ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ B ≥ 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
    ‖f n‖ ≤ B * scale n * Real.exp (C * (1 + Real.log (n : ℝ)))

theorem FixedPolynomialBound.add {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    {f g : ℕ → ℂ} (hf : FixedPolynomialBound s f) (hg : FixedPolynomialBound s g) :
    FixedPolynomialBound s (fun n => f n + g n) := by
  obtain ⟨B, hB, C, hC, hf⟩ := hf
  obtain ⟨D, hD, E, hE, hg⟩ := hg
  refine ⟨B + D, by positivity, C + E, by positivity, ?_⟩
  filter_upwards [hf, hg, eventually_ge_atTop (1 : ℕ)] with n hnF hnG hn1
  have hlog : 0 ≤ 1 + Real.log (n : ℝ) := by have h := Real.log_nonneg (by exact_mod_cast hn1 : (1 : ℝ) ≤ n); linarith
  have hfe : Real.exp (C * (1 + Real.log (n : ℝ))) ≤ Real.exp ((C + E) * (1 + Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hE hlog])
  have hge : Real.exp (E * (1 + Real.log (n : ℝ))) ≤ Real.exp ((C + E) * (1 + Real.log (n : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hC hlog])
  have hf' := hnF.trans (mul_le_mul_of_nonneg_left hfe (mul_nonneg hB (hs n)))
  have hg' := hnG.trans (mul_le_mul_of_nonneg_left hge (mul_nonneg hD (hs n)))
  exact (norm_add_le _ _).trans (by nlinarith [hf', hg'])

theorem FixedPolynomialBound.const_mul {s : ℕ → ℝ} {f : ℕ → ℂ}
    (hf : FixedPolynomialBound s f) (w : ℂ) : FixedPolynomialBound s (fun n => w * f n) := by
  obtain ⟨B, hB, C, hC, hb⟩ := hf
  refine ⟨‖w‖ * B, by positivity, C, hC, ?_⟩
  filter_upwards [hb] with n hn
  rw [norm_mul]
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg w)]

theorem FixedPolynomialBound.sub {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    {f g : ℕ → ℂ} (hf : FixedPolynomialBound s f) (hg : FixedPolynomialBound s g) :
    FixedPolynomialBound s (fun n => f n - g n) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add hs (hg.const_mul (-1))

theorem fixedPolynomialBound_integral {s : ℕ → ℝ} {f : ℕ → ℂ → ℂ}
    {K : Set ℂ} {a b : ℝ} {γ : ℝ → ℂ}
    (hγ : ∀ u ∈ uIcc a b, γ u ∈ K) (w : ℂ)
    (hb : ∃ B ≥ 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ x ∈ K,
      ‖f n x‖ ≤ B * s n * Real.exp (C * (1 + Real.log (n : ℝ)))) :
    FixedPolynomialBound s (fun n => ∫ u in a..b, w * f n (γ u)) := by
  obtain ⟨B, hB, C, hC, hb⟩ := hb
  refine ⟨|b - a| * ‖w‖ * B, by positivity, C, hC, ?_⟩
  filter_upwards [hb] with n hn
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun u => w * f n (γ u))
    (C := ‖w‖ * (B * s n * Real.exp (C * (1 + Real.log (n : ℝ))))) (fun u hu => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hn _ (hγ u (uIoc_subset_uIcc hu))) (norm_nonneg _))
  nlinarith [h]

theorem fixedPolynomialBound_boundary_path {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ)
    {γ : ℝ → ℂ} {a b : ℝ} (hc : ContinuousOn γ (uIcc a b))
    (hslit : ∀ u ∈ uIcc a b, γ u ∈ Complex.slitPlane)
    (hleft : ∀ u ∈ uIcc a b, (γ u).re < 1) (w : ℂ) :
    FixedPolynomialBound (commonScale r m A z)
      (fun n => ∫ u in a..b, w * boundaryKernel r m A z n (γ u)) := by
  apply fixedPolynomialBound_integral (K := γ '' uIcc a b) (fun u hu => ⟨u, hu, rfl⟩) w
  exact uniform_boundaryKernel_fixed_compact_bound hr hA hz m
    (isCompact_uIcc.image_of_continuousOn hc)
    (by rintro x ⟨u, hu, rfl⟩; exact hslit u hu)
    (by rintro x ⟨u, hu, rfl⟩; exact hleft u hu)

theorem fixedPolynomialBound_reflected_path {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ)
    {γ : ℝ → ℂ} {a b : ℝ} (hc : ContinuousOn γ (uIcc a b))
    (hleft : ∀ u ∈ uIcc a b, (γ u).re < 1) (w : ℂ) :
    FixedPolynomialBound (commonScale r m A z)
      (fun n => ∫ u in a..b, w * reflectedKernel r m A z n (γ u)) := by
  apply fixedPolynomialBound_integral (K := γ '' uIcc a b) (fun u hu => ⟨u, hu, rfl⟩) w
  exact uniform_reflectedKernel_fixed_compact_bound hr hA hz m
    (isCompact_uIcc.image_of_continuousOn hc)
    (by rintro x ⟨u, hu, rfl⟩; exact hleft u hu)

theorem boundaryFixedCorrection_polynomial_bound {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z L : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (m : ℕ) (hL : L ≤ 1 / 2) :
    FixedPolynomialBound (commonScale r m A z) (fun n => boundaryFixedCorrection r m A z n L) := by
  have hs (n : ℕ) := (commonScale_pos hA hz m n).le
  have hleft (u : ℝ) (hu : u ∈ uIcc L (1 / 2 : ℝ)) : u < 1 := by
    rw [uIcc_of_le hL] at hu
    linarith [hu.2]
  have hp := fixedPolynomialBound_boundary_path hr hA hz m
    (γ := fun u : ℝ => (u : ℂ) + Complex.I) (a := L) (b := 1 / 2) (by fun_prop)
    (fun u _ => Complex.mem_slitPlane_iff.mpr (Or.inr (by simp)))
    (fun u hu => by simpa using hleft u hu) 1
  have hm := fixedPolynomialBound_boundary_path hr hA hz m
    (γ := fun u : ℝ => (u : ℂ) - Complex.I) (a := L) (b := 1 / 2) (by fun_prop)
    (fun u _ => Complex.mem_slitPlane_iff.mpr (Or.inr (by simp)))
    (fun u hu => by simpa using hleft u hu) 1
  have hv := fixedPolynomialBound_boundary_path hr hA hz m
    (γ := fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * Complex.I) (a := -1) (b := 1) (by fun_prop)
    (fun u _ => Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num [Complex.mul_re])))
    (fun u _ => by norm_num [Complex.mul_re]) Complex.I
  have hq := fixedPolynomialBound_reflected_path hr hA hz m
    (γ := fun u : ℝ => (L : ℂ) + (u : ℂ) * Complex.I) (a := -1) (b := 0) (by fun_prop)
    (fun u _ => by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]; linarith) Complex.I
  simpa only [one_mul, boundaryFixedCorrection] using
    ((hm.sub hs hp).add hs hv).sub hs (hq.const_mul (2 * (Real.pi : ℂ) * Complex.I))

end ThisWork.HigherRank
