module

public import ThisWork.WindowOrientation
public import ThisWork.CompactMomentRemainder

/-! Uniform separation of the contour outside its local saddle window. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

def OutsideSaddleWindow (j : Branch) (σ : ℂ) (a b : ℝ) (s : ℂ) : Prop :=
  match j with
  | .one | .two => s.im ≠ σ.im ∨ s.re ≤ σ.re - a ∨ σ.re + b ≤ s.re
  | .three => s.re ≠ σ.re ∨ s.im ≤ σ.im - a ∨ σ.im + b ≤ s.im

theorem contour_gap_outside_window {c a b : ℝ} (hc : 0 < c)
    (ha : a < c / 16) (hb : b < c / 16) (j : Branch) {σ s : ℂ}
    (hσ : σ ∈ saddleDisk c j)
    (hs : s ∈ hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ))
    (hout : OutsideSaddleWindow j σ a b s) :
    min a b ≤ ‖s - σ‖ := by
  have hre : |s.re - σ.re| ≤ ‖s - σ‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - σ)
  have him : |s.im - σ.im| ≤ ‖s - σ‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s - σ)
  have hside := saddleDisk_im_side hc j hσ
  have hregion := saddleDisk_region hc j hσ
  have hδ : min a b < c / 16 := by simpa only [min_self] using min_lt_min ha hb
  by_contra! hgap
  have hrb := abs_le.mp hre
  have hib := abs_le.mp him
  cases j
  · change σ.im ≤ -(c / 4) at hside
    change σ.re ≤ -(c / 4) ∧ _ at hregion
    have hi : σ.im ≤ 0 := by linarith
    rw [mem_hankelTrace_iff] at hs
    simp only [saddleContourRight, saddleContourHeight, abs_of_nonpos hi, neg_neg] at hs
    change s.im ≠ σ.im ∨ s.re ≤ σ.re - a ∨ σ.re + b ≤ s.re at hout
    rcases hs with (⟨_, him⟩ | ⟨hr, _, _⟩) | ⟨_, him⟩
    · rcases hout with hne | hl | hr
      · exact hne him
      · linarith [min_le_left a b]
      · linarith [min_le_right a b]
    · linarith [hregion.1]
    · linarith
  · change c / 4 ≤ σ.im at hside
    change σ.re ≤ -(c / 4) ∧ _ at hregion
    have hi : 0 ≤ σ.im := by linarith
    rw [mem_hankelTrace_iff] at hs
    simp only [saddleContourRight, saddleContourHeight, abs_of_nonneg hi] at hs
    change s.im ≠ σ.im ∨ s.re ≤ σ.re - a ∨ σ.re + b ≤ s.re at hout
    rcases hs with (⟨_, him⟩ | ⟨hr, _, _⟩) | ⟨_, him⟩
    · linarith
    · linarith [hregion.1]
    · rcases hout with hne | hl | hr
      · exact hne him
      · linarith [min_le_left a b]
      · linarith [min_le_right a b]
  · change |σ.im| ≤ c / 4 at hside
    have his := abs_le.mp hside
    rw [mem_hankelTrace_iff] at hs
    simp only [saddleContourRight, saddleContourHeight] at hs
    change s.re ≠ σ.re ∨ s.im ≤ σ.im - a ∨ σ.im + b ≤ s.im at hout
    rcases hs with (⟨_, him⟩ | ⟨hr, _, _⟩) | ⟨_, him⟩
    · linarith
    · rcases hout with hne | hl | hu
      · exact hne hr
      · linarith [min_le_left a b]
      · linarith [min_le_right a b]
    · linarith

theorem bounded_saddleContour_norm {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (j : Branch)
    {σ s : ℂ} (hσ : σ ∈ saddleDisk c j)
    (hs : s ∈ hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ))
    (hleft : -T ≤ s.re) : ‖s‖ ≤ T + 4 * c := by
  have hr := saddleContourRight_bounds hc j hσ
  have hh := saddleContourHeight_bounds hc j hσ
  have hh0 : 0 ≤ saddleContourHeight c j σ := by linarith
  have hcoords : s.re ≤ saddleContourRight c j σ ∧ |s.im| ≤ saddleContourHeight c j σ := by
    rcases mem_hankelTrace_iff.mp hs with (⟨hre, him⟩ | ⟨hre, hlo, hhi⟩) | ⟨hre, him⟩
    · exact ⟨hre, by rw [him, abs_neg, abs_of_nonneg hh0]⟩
    · exact ⟨hre.le, abs_le.mpr ⟨hlo, hhi⟩⟩
    · exact ⟨hre, by rw [him, abs_of_nonneg hh0]⟩
  have hRe : |s.re| ≤ T + 2 * c := abs_le.mpr ⟨by linarith, by linarith [hcoords.1]⟩
  have hIm : |s.im| ≤ 2 * c := hcoords.2.trans hh.2
  have hn : ‖s‖ ≤ |s.re| + |s.im| := by
    calc
      _ = ‖(s.re : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp
  linarith

theorem uniform_moment_window_remainder_piece {α₁ α₂ a b T : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (ha0 : 0 < a) (hb0 : 0 < b) (hT : 0 ≤ T)
    (ha : a < saddleScale α₁ α₂ / 16) (hb : b < saddleScale α₁ α₂ / 16)
    (j : Branch) (D : ℝ) (k : ℕ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ∀ (l u : ℝ) (v : ℂ) (γ : ℝ → ℂ),
      (∀ t ∈ uIcc l u, γ t ∈ hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
        (saddleContourHeight (saddleScale α₁ α₂) j σ) ∧ -T ≤ (γ t).re ∧
        OutsideSaddleWindow j σ a b (γ t)) →
      ‖∫ t in l..u, v * ((γ t) ^ k * kernel α₁ α₂ j n ((largeScale n : ℂ) * γ t))‖ ≤
        (‖v‖ * (T + 4 * saddleScale α₁ α₂) ^ k *
          ‖kernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-ε * largeScale n)) * |u - l| := by
  obtain ⟨ε, hε, hc⟩ := uniform_moment_compact_integral_gap h₁ h₂
    (lt_min ha0 hb0) j (T + 4 * saddleScale α₁ α₂) D k
  refine ⟨ε, hε, hc.mono (fun n hn σ hσ hdisp l u v γ hγ => ?_)⟩
  apply hn σ hσ hdisp l u v γ
  intro t ht
  obtain ⟨hs, hl, ho⟩ := hγ t ht
  exact ⟨hs, bounded_saddleContour_norm (saddleScale_pos h₁ h₂) hT j hσ hs hl,
    contour_gap_outside_window (saddleScale_pos h₁ h₂) ha hb j hσ hs ho⟩

end ThisWork
