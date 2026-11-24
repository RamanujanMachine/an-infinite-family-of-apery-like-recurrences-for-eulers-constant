module

public import ThisWork.HigherRank.HankelTranslations

/-! The original Gamma integrals on translated and scaled Hankel contours. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter MeasureTheory
open scoped Topology

theorem branchIntegral_eq_scaled_shifted {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) (k : Fin r)
    {R right height : ℝ} {δ : ℂ} (hR : 0 < R) (hright0 : 0 < R * (right + δ.re))
    (hright : ∀ i, R * (right + δ.re) < A i * n + 1)
    (hlow : R * (-height + δ.im) ≤ -1) (hhigh : 1 ≤ R * (height + δ.im)) :
    branchIntegral r b A z j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((R : ℂ) * shiftedHankelIntegral right height δ
        (fun s => ((b : ℂ) * n - (R : ℂ) * s) ^ k.val * kernel r b A z j n ((R : ℂ) * s))) := by
  let f : ℂ → ℂ := fun x => ((b : ℂ) * n - x) ^ k.val * kernel r b A z j n x
  have htrans := shiftedHankelIntegral_eq_asymmetric (R * right) (R * height) ((R : ℂ) * δ) f
  have hre : R * right + ((R : ℂ) * δ).re = R * (right + δ.re) := by simp [Complex.mul_re]; ring
  have hlo : -(R * height) + ((R : ℂ) * δ).im = R * (-height + δ.im) := by simp [Complex.mul_im]; ring
  have hhi : R * height + ((R : ℂ) * δ).im = R * (height + δ.im) := by simp [Complex.mul_im]; ring
  rw [hre, hlo, hhi] at htrans
  rw [branchIntegral_eq_asymmetric hr hA b z j n k hright0 hright hlow hhigh, ← htrans,
    shiftedHankelIntegral_scale f right height δ hR]

theorem integrableOn_scaled_shifted_weighted_horizontal {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    {R right y : ℝ} {δ : ℂ} (hR : 0 < R)
    (hright : ∀ i, R * (right + δ.re) < A i * n + 1) (hy : 1 ≤ |R * (y + δ.im)|) :
    IntegrableOn (fun u : ℝ => ((b : ℂ) * n - (R : ℂ) * (δ + (u : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      kernel r b A z j n ((R : ℂ) * (δ + (u : ℂ) + (y : ℂ) * Complex.I))) (Iic right) := by
  let g : ℝ → ℂ := fun u => ((b : ℂ) * n - ((u : ℂ) + ((R * (y + δ.im) : ℝ) : ℂ) * Complex.I)) ^ k *
    kernel r b A z j n ((u : ℂ) + ((R * (y + δ.im) : ℝ) : ℂ) * Complex.I)
  have hg : IntegrableOn g (Iic (R * (right + δ.re))) :=
    integrableOn_weighted_kernel_horizontal hr hA b z j n k hright hy
  have hs := (Analytic.integrableOn_comp_mul_left_Iic_iff g (right + δ.re) hR).mpr hg
  have ht := integrableOn_comp_add_Iic (a := right) (c := δ.re) hs
  apply ht.congr_fun _ measurableSet_Iic
  intro u _
  have hx : ((R * (u + δ.re) : ℝ) : ℂ) + ((R * (y + δ.im) : ℝ) : ℂ) * Complex.I =
      (R : ℂ) * (δ + (u : ℂ) + (y : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero] <;> ring
  change g (R * (u + δ.re)) = _
  dsimp only [g]
  rw [hx]

end ThisWork.HigherRank
