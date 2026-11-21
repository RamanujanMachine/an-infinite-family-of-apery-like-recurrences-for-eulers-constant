module

public import ThisWork.Trajectory.TailIntegrals
public import ThisWork.Trajectory.SqrtContourGap

/-! Exponentially small integrated tails relative to the actual canonical saddle kernel. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric MeasureTheory Analytic
open scoped Topology

private theorem canonical_anchor_properties {c a y : ℝ} {σ : ℂ}
    (hc : 0 < c) (ha : 2 * c ≤ a) (hσ : σ ∈ saddleDisk c .three) (hy : |y| = c) :
    (-(a : ℂ) + (y : ℂ) * Complex.I) ∈
      hankelTrace (saddleContourRight c .three σ) (saddleContourHeight c .three σ) ∧
      ‖-(a : ℂ) + (y : ℂ) * Complex.I‖ ≤ a + c ∧
      c / 4 ≤ ‖(-(a : ℂ) + (y : ℂ) * Complex.I) - σ‖ := by
  have hsre : c / 2 ≤ σ.re := saddleDisk_region hc .three hσ
  have ha0 : 0 ≤ a := by linarith
  refine ⟨?_, ?_, ?_⟩
  · change (-(a : ℂ) + (y : ℂ) * Complex.I) ∈ hankelTrace σ.re c
    rcases le_or_gt 0 y with h | h
    · have he : y = c := by simpa only [abs_of_nonneg h] using hy
      exact Or.inr ⟨-a, by linarith, by simp [he]⟩
    · have he : y = -c := by rw [abs_of_neg h] at hy; linarith
      exact Or.inl (Or.inl ⟨-a, by linarith, by simp [he]⟩)
  · simpa only [Nat.cast_zero, zero_sub, norm_neg, zero_add] using
      norm_polynomial_left_le ha0 hy.le 0
  · have h := Complex.re_le_norm (σ - (-(a : ℂ) + (y : ℂ) * Complex.I))
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, zero_mul, add_zero] at h
    rw [norm_sub_rev] at h
    linarith

/-- The two infinite canonical contour rays are exponentially negligible for every
fixed power moment, with all constants uniform in the moving saddle center. -/
theorem uniform_integrated_canonical_tail {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m k : ℕ) (D : ℝ) :
    ∃ a ≥ 1, 2 * doubleSaddleScale d A₁ A₂ z ≤ a ∧
      ∃ ε > 0, ∃ B ≥ 0, ∀ᶠ n : ℕ in atTop,
      ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
        ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
        ∀ y : ℝ, |y| = doubleSaddleScale d A₁ A₂ z →
          IntegrableOn (leftMomentKernel m d A₁ A₂ z .three n k y) (Ioi a) ∧
          ‖∫ t in Ioi a, leftMomentKernel m d A₁ A₂ z .three n k y t‖ ≤
            B * ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨T, hT, hI⟩ := uniform_integrated_leftMoment_tail hd h₁ h₂ hz
    (η := c / 2) (H := c) (q := 1) (by positivity) hc.le zero_lt_one m .three k
  let a := max T (2 * c + 1)
  have ha : 1 ≤ a := hT.trans (le_max_left _ _)
  have ha₂ : 2 * c ≤ a := (by linarith : 2 * c ≤ 2 * c + 1).trans (le_max_right _ _)
  obtain ⟨ε, hε, hgap⟩ := uniform_kernel_compact_gap hd h₁ h₂ hz (δ := c / 4)
    (by positivity) m (a + c) D
  refine ⟨a, ha, ha₂, ε, hε, Real.exp a, (Real.exp_pos _).le, ?_⟩
  filter_upwards [hI, hgap, sqrtScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hi hg hR σ hσ hdisp y hy
  have hanchor := canonical_anchor_properties hc ha₂ hσ hy
  have hK := hg σ hσ hdisp _ hanchor.1 hanchor.2.1 hanchor.2.2
  obtain ⟨hInt, hBound⟩ := hi a (le_max_left _ _) y
    (by rw [hy]; linarith) (by rw [hy])
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ Real.exp a * ‖kernel m d A₁ A₂ z .three n
        ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ / sqrtScale n := by
      simpa only [one_mul] using hBound
    _ ≤ Real.exp a * ‖kernel m d A₁ A₂ z .three n
        ((sqrtScale n : ℂ) * (-(a : ℂ) + (y : ℂ) * Complex.I))‖ :=
      div_le_self (by positivity) hR
    _ ≤ Real.exp a * (‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ *
        Real.exp (-ε * sqrtScale n)) := mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
    _ = _ := by ring

end ThisWork.Trajectory
