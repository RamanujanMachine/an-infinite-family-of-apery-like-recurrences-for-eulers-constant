module

public import ThisWork.HigherRank.ParabolicPhase
public import ThisWork.HigherRank.SaddleEquation

/-! Uniform pole-free regions for parabolic contours translated to the exact
saddles. A fixed translation bound works on the entire unbounded parabola. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter

theorem parabolicPoint_re (a b : ℝ) :
    (parabolicPoint a b).re = a ^ 2 - b ^ 2 := by
  simp [parabolicPoint, pow_two, Complex.mul_re]

theorem parabolicPoint_im (a b : ℝ) :
    (parabolicPoint a b).im = 2 * a * b := by
  simp [parabolicPoint, pow_two, Complex.mul_im]
  ring

theorem norm_parabolicPoint (a b : ℝ) : ‖parabolicPoint a b‖ = a ^ 2 + b ^ 2 := by
  rw [parabolicPoint, norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem hasDerivAt_parabolicPoint (a b : ℝ) :
    HasDerivAt (parabolicPoint a) (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) b := by
  convert ((hasDerivAt_const b (a : ℂ)).add
    (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I)).pow 2 using 1
  · rfl
  · simp
    ring

theorem translated_parabola_region {a : ℝ} (ha : 0 < a) {δ : ℂ}
    (hδ : ‖δ‖ ≤ a ^ 2 / 8) (b : ℝ) :
    a ^ 2 / 4 ≤ (δ + parabolicPoint a b).re ∨
      a ^ 2 / 4 ≤ |(δ + parabolicPoint a b).im| := by
  have hdre : -a ^ 2 / 8 ≤ δ.re := by
    linarith [neg_le_abs δ.re, Complex.abs_re_le_norm δ]
  have hdim : |δ.im| ≤ a ^ 2 / 8 := (Complex.abs_im_le_norm δ).trans hδ
  by_cases hb : |b| ≤ a / 2
  · left
    rw [Complex.add_re, parabolicPoint_re]
    have hb2 : |b| ^ 2 ≤ (a / 2) ^ 2 := (sq_le_sq₀ (abs_nonneg b) (by positivity)).mpr hb
    rw [sq_abs] at hb2
    nlinarith [sq_nonneg a]
  · right
    have hb' : a / 2 < |b| := lt_of_not_ge hb
    have hi : |(parabolicPoint a b).im| = 2 * a * |b| := by
      rw [parabolicPoint_im, abs_mul, abs_of_pos (by positivity : 0 < 2 * a)]
    have hl := norm_sub_norm_le ((parabolicPoint a b).im) (-δ.im)
    simp only [Real.norm_eq_abs, abs_neg, sub_neg_eq_add] at hl
    rw [hi] at hl
    rw [Complex.add_im, add_comm]
    nlinarith

theorem parabolic_gaussian_coefficient (r : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ((r : ℂ) / parabolicPoint a b) *
      (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2 = -4 * (r : ℂ) := by
  have hs : parabolicPoint a b ≠ 0 := Complex.slitPlane_ne_zero (parabolicPoint_mem_slitPlane ha b)
  have ht : (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2 =
      -4 * parabolicPoint a b := by
    rw [mul_pow, mul_pow, Complex.I_sq]
    unfold parabolicPoint
    ring
  rw [ht]
  field_simp

theorem norm_translated_parabola_le {a B b : ℝ} {δ : ℂ}
    (hδ : ‖δ‖ ≤ a ^ 2 / 8) (hb : |b| ≤ B) :
    ‖δ + parabolicPoint a b‖ ≤ a ^ 2 / 8 + a ^ 2 + B ^ 2 := by
  have hb2 : b ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg b) ((abs_nonneg b).trans hb)).mpr hb
  calc
    _ ≤ ‖δ‖ + ‖parabolicPoint a b‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_parabolicPoint]; linarith

/-- One error estimate works for every small translation of the finite arc;
in particular the translation may be the displacement of an exact saddle. -/
theorem uniform_exactSaddleEquation_parabola {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ ≤ a ^ 2 / 8 →
      ∀ b : ℝ, |b| ≤ B →
        ‖exactSaddleEquation r A z j n (δ + parabolicPoint a b) -
          limitingEquation r A z j (δ + parabolicPoint a b)‖ ≤ C * smallParameter r n := by
  obtain ⟨C, hC, h⟩ := uniform_exactSaddleEquation_region hr hA z j
    (by positivity : 0 < a ^ 2 / 4) (by positivity : 0 < a ^ 2 / 4)
    (by positivity : 0 ≤ a ^ 2 / 8 + a ^ 2 + B ^ 2)
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with n hn δ hδ b hb
  exact hn _ (norm_translated_parabola_le hδ hb) (translated_parabola_region ha hδ b)

theorem eventually_translated_parabola_in_kernelDomain {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ ≤ a ^ 2 / 8 → ∀ b : ℝ,
      (largeScale r n : ℂ) * (δ + parabolicPoint a b) ∈ kernelDomain r A n := by
  filter_upwards [eventually_scaled_region_in_kernelDomain hr hA
    (by positivity : 0 < a ^ 2 / 4) (by positivity : 0 < a ^ 2 / 4)
    (a ^ 2 / 8 + a ^ 2)] with n hn δ hδ b
  apply hn _ _ (translated_parabola_region ha hδ b)
  rw [Complex.add_re, parabolicPoint_re]
  linarith [Complex.re_le_norm δ, sq_nonneg b]

end ThisWork.HigherRank
