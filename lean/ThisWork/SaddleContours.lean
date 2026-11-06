module

public import ThisWork.HankelDeformation

/-! Admissible polygonal contours through the moving exact saddles. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable def saddleContourRight (c : ℝ) (j : Branch) (s : ℂ) : ℝ :=
  match j with
  | .one | .two => c / 2
  | .three => s.re

noncomputable def saddleContourHeight (c : ℝ) (j : Branch) (s : ℂ) : ℝ :=
  match j with
  | .one | .two => |s.im|
  | .three => c

theorem saddleContourRight_bounds {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ}
    (hs : s ∈ saddleDisk c j) :
    0 < saddleContourRight c j s ∧ saddleContourRight c j s ≤ 2 * c := by
  have hr := saddleDisk_region hc j hs
  have hn := saddleDisk_norm_le hc j hs
  cases j <;> simp only [saddleContourRight, saddleRegion] at *
  all_goals constructor <;> nlinarith [le_abs_self s.re, Complex.abs_re_le_norm s]

theorem saddleContourHeight_bounds {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ}
    (hs : s ∈ saddleDisk c j) :
    c / 4 ≤ saddleContourHeight c j s ∧ saddleContourHeight c j s ≤ 2 * c := by
  have hr := saddleDisk_region hc j hs
  have hn := saddleDisk_norm_le hc j hs
  cases j <;> simp only [saddleContourHeight, saddleRegion] at *
  all_goals constructor <;> nlinarith [Complex.abs_im_le_norm s]

theorem mem_hankelTrace_of_re_le {r : ℝ} {s : ℂ} (hs : s.re ≤ r) :
    s ∈ hankelTrace r |s.im| := by
  rcases le_total 0 s.im with hi | hi
  · exact Or.inr ⟨s.re, hs, by rw [abs_of_nonneg hi]; exact (Complex.re_add_im s).symm⟩
  · exact Or.inl (Or.inl ⟨s.re, hs, by
      rw [abs_of_nonpos hi, neg_neg]
      exact (Complex.re_add_im s).symm⟩)

theorem saddle_mem_saddleContour {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ}
    (hs : s ∈ saddleDisk c j) :
    s ∈ hankelTrace (saddleContourRight c j s) (saddleContourHeight c j s) := by
  have hr := saddleDisk_region hc j hs
  cases j
  · exact mem_hankelTrace_of_re_le (by change s.re ≤ -(c / 4) ∧ _ at hr; dsimp [saddleContourRight]; linarith [hr.1])
  · exact mem_hankelTrace_of_re_le (by change s.re ≤ -(c / 4) ∧ _ at hr; dsimp [saddleContourRight]; linarith [hr.1])
  · have hd : ‖s - (c : ℂ)‖ ≤ c / 4 := by
      simpa only [saddleDisk, mem_closedBall, dist_eq_norm, rho_three, mul_one] using hs
    have hi : |s.im| ≤ c / 4 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
        (Complex.abs_im_le_norm (s - (c : ℂ))).trans hd
    change s ∈ hankelTrace s.re c
    exact Or.inl (Or.inr ⟨s.im, ⟨by linarith [(abs_le.mp hi).1], by linarith [(abs_le.mp hi).2]⟩,
      (Complex.re_add_im s).symm⟩)

theorem hankelTrace_scale {R r h : ℝ} (hR : 0 ≤ R) {s : ℂ}
    (hs : s ∈ hankelTrace r h) : (R : ℂ) * s ∈ hankelTrace (R * r) (R * h) := by
  rcases hs with (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩) | ⟨u, hu, rfl⟩
  · exact Or.inl (Or.inl ⟨R * u, mul_le_mul_of_nonneg_left hu hR, by push_cast; ring⟩)
  · exact Or.inl (Or.inr ⟨R * v, ⟨by nlinarith [mul_le_mul_of_nonneg_left hv.1 hR],
      mul_le_mul_of_nonneg_left hv.2 hR⟩, by push_cast; ring⟩)
  · exact Or.inr ⟨R * u, mul_le_mul_of_nonneg_left hu hR, by push_cast; ring⟩

theorem eventually_saddleContours_admissible {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      0 < largeScale n * saddleContourRight (saddleScale α₁ α₂) j s ∧
      largeScale n * saddleContourRight (saddleScale α₁ α₂) j s <
        min (α₁ * n + 1) (α₂ * n + 1) ∧
      1 ≤ largeScale n * saddleContourHeight (saddleScale α₁ α₂) j s ∧
      (largeScale n : ℂ) * s ∈ hankelTrace
        (largeScale n * saddleContourRight (saddleScale α₁ α₂) j s)
        (largeScale n * saddleContourHeight (saddleScale α₁ α₂) j s) := by
  have hc := saddleScale_pos h₁ h₂
  filter_upwards [eventually_right_factor_conditions h₁ (2 * saddleScale α₁ α₂),
    eventually_right_factor_conditions h₂ (2 * saddleScale α₁ α₂),
    largeScale_tendsto.eventually (eventually_ge_atTop (4 / saddleScale α₁ α₂)),
    eventually_gt_atTop (0 : ℕ)] with n hn₁ hn₂ hsize hn
  refine ⟨hn, fun s hs => ?_⟩
  obtain ⟨hr₀, hr⟩ := saddleContourRight_bounds hc j hs
  have hR := largeScale_pos hn
  refine ⟨mul_pos hR hr₀, lt_min
    (by nlinarith [mul_le_mul_of_nonneg_left hr hR.le, hn₁.1, hn₁.2])
    (by nlinarith [mul_le_mul_of_nonneg_left hr hR.le, hn₂.1, hn₂.2]), ?_,
    hankelTrace_scale hR.le (saddle_mem_saddleContour hc j hs)⟩
  nlinarith [(div_le_iff₀ hc).mp hsize,
    mul_le_mul_of_nonneg_left (saddleContourHeight_bounds hc j hs).1 hR.le]

theorem eventually_branchIntegral_eq_saddleContour {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, ∀ s ∈ saddleDisk (saddleScale α₁ α₂) j, ∀ k : Fin 3,
      branchIntegral α₁ α₂ j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        hankelIntegral (largeScale n * saddleContourRight (saddleScale α₁ α₂) j s)
          (largeScale n * saddleContourHeight (saddleScale α₁ α₂) j s)
          (fun x => ((n : ℂ) - x) ^ k.val * kernel α₁ α₂ j n x) := by
  exact (eventually_saddleContours_admissible h₁ h₂ j).mono fun n hn s hs k =>
    branchIntegral_eq_deformed h₁ h₂ j n k (hn.2 s hs).1 (hn.2 s hs).2.1 (hn.2 s hs).2.2.1

/-- For every sufficiently large index, the original vector integral has an
admissible contour through a simple exact stationary point of its actual kernel. -/
theorem exists_exact_saddle_contour {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∃ s ∈ saddleDisk (saddleScale α₁ α₂) j,
      deriv (kernel α₁ α₂ j n) ((largeScale n : ℂ) * s) = 0 ∧
      deriv (exactSaddleEquation α₁ α₂ j n) s ≠ 0 ∧
      ‖s - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ C * smallParameter n ∧
      (largeScale n : ℂ) * s ∈ hankelTrace
        (largeScale n * saddleContourRight (saddleScale α₁ α₂) j s)
        (largeScale n * saddleContourHeight (saddleScale α₁ α₂) j s) ∧
      ∀ k : Fin 3, branchIntegral α₁ α₂ j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        hankelIntegral (largeScale n * saddleContourRight (saddleScale α₁ α₂) j s)
          (largeScale n * saddleContourHeight (saddleScale α₁ α₂) j s)
          (fun x => ((n : ℂ) - x) ^ k.val * kernel α₁ α₂ j n x) := by
  obtain ⟨C, hC, hb⟩ := exists_exact_kernel_saddle h₁ h₂ j
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_saddleContours_admissible h₁ h₂ j,
    eventually_branchIntegral_eq_saddleContour h₁ h₂ j] with n hn ha hi
  obtain ⟨s, hs, _, hz, hd, he⟩ := hn
  exact ⟨s, hs, hz, hd, he, (ha.2 s hs).2.2.2, hi s hs⟩

end ThisWork
