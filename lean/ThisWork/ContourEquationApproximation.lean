module

public import ThisWork.ImaginaryDigamma
public import ThisWork.CompactContourGap

/-! Uniform exact-equation approximation on the bounded contour regions. -/

public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem uniform_exactSaddleEquation_region {α₁ α₂ κ η M ε : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hκ : 0 < κ) (hη : 0 < η)
    (hε : 0 < ε) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤ ε := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((11 + 3 * M) / (2 * α₁) + (11 + 3 * M) / (2 * α₂)) * smallParameter n ≤ ε / 2 := by
    have hlim : Tendsto (fun n =>
        ((11 + 3 * M) / (2 * α₁) + (11 + 3 * M) / (2 * α₂)) * smallParameter n) atTop (𝓝 0) := by
      simpa only [mul_zero] using smallParameter_tendsto.const_mul
        ((11 + 3 * M) / (2 * α₁) + (11 + 3 * M) / (2 * α₂))
    exact (hlim.eventually (gt_mem_nhds (half_pos hε))).mono fun _ h => h.le
  filter_upwards [largeScale_tendsto.eventually (uniform_scaled_digamma_region hκ hη
    (show 0 < ε / 6 by positivity)), eventually_right_factor_conditions h₁ M,
    eventually_right_factor_conditions h₂ M, hsmall, eventually_ge_atTop (1 : ℕ)]
    with n hψ hA₁ hA₂ herr hn
  refine ⟨by omega, fun s hs hregion => ?_⟩
  have hs₀ : s ≠ 0 := by
    intro he
    rw [he, Complex.zero_re, Complex.zero_im, abs_zero] at hregion
    rcases hregion with h | h <;> linarith
  have hp := norm_exactSaddleEquation_sub_limit_le h₁ h₂ j (by omega : 0 < n) hs hs₀
    hA₁.1 hA₂.1 hA₁.2 hA₂.2
  nlinarith [hψ.2 s hregion, affineError_le_smallParameter h₁ hn M, affineError_le_smallParameter h₂ hn M]

theorem saddleContourRight_lower {c : ℝ} (hc : 0 < c) (j : Branch) {σ : ℂ}
    (hσ : σ ∈ saddleDisk c j) : c / 2 ≤ saddleContourRight c j σ := by
  cases j
  · exact le_rfl
  · exact le_rfl
  · exact saddleDisk_region hc .three hσ

theorem saddleContour_mem_region {c : ℝ} (hc : 0 < c) (j : Branch) {σ s : ℂ}
    (hσ : σ ∈ saddleDisk c j)
    (hs : s ∈ hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ)) :
    c / 4 ≤ s.re ∨ c / 4 ≤ |s.im| := by
  have hh := (saddleContourHeight_bounds hc j hσ).1
  rcases mem_hankelTrace_iff.mp hs with ((⟨_, him⟩ | ⟨hre, _⟩) | ⟨_, him⟩)
  · right
    rw [him, abs_neg, abs_of_nonneg ((show 0 ≤ c / 4 by positivity).trans hh)]
    exact hh
  · left
    rw [hre]
    exact (by linarith : c / 4 ≤ c / 2).trans (saddleContourRight_lower hc j hσ)
  · right
    rw [him, abs_of_nonneg ((show 0 ≤ c / 4 by positivity).trans hh)]
    exact hh

theorem uniform_exactSaddleEquation_contours {α₁ α₂ ε : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hε : 0 < ε) (j : Branch) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
        (saddleContourHeight (saddleScale α₁ α₂) j σ) → ‖s‖ ≤ M →
      ‖exactSaddleEquation α₁ α₂ j n s - limitingEquation j (saddleScale α₁ α₂) s‖ ≤ ε := by
  have hc := saddleScale_pos h₁ h₂
  exact (uniform_exactSaddleEquation_region h₁ h₂
    (κ := saddleScale α₁ α₂ / 4) (η := saddleScale α₁ α₂ / 4) (M := M)
    (by positivity) (by positivity) hε j).mono fun n hn =>
      ⟨hn.1, fun σ hσ s hs hM => hn.2 s hM (saddleContour_mem_region hc j hσ hs)⟩

end ThisWork
