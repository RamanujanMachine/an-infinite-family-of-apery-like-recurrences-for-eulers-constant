module

public import ThisWork.ContourBounds

/-! Explicit fixed Hankel contours for the three limiting phases. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

noncomputable def complexHeight (c : ℝ) : ℝ := Real.sqrt 3 * c / 2

noncomputable def complexRight (c : ℝ) : ℝ := c / 2

/-- Lower horizontal ray, right vertical edge, and upper horizontal ray. -/
def hankelTrace (right height : ℝ) : Set ℂ :=
  {s | ∃ x ≤ right, s = (x : ℂ) + (-height : ℝ) * Complex.I} ∪
  {s | ∃ y ∈ Icc (-height) height, s = (right : ℂ) + (y : ℂ) * Complex.I} ∪
  {s | ∃ x ≤ right, s = (x : ℂ) + (height : ℂ) * Complex.I}

theorem complexHeight_pos {c : ℝ} (hc : 0 < c) : 0 < complexHeight c := by
  apply div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc) (by norm_num)

theorem complexRight_pos {c : ℝ} (hc : 0 < c) : 0 < complexRight c := half_pos hc

theorem complexRight_sq_add_height_sq (c : ℝ) :
    complexRight c ^ 2 + complexHeight c ^ 2 = c ^ 2 := by
  dsimp [complexRight, complexHeight, neg_div]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem lower_saddle_coordinates (c : ℝ) :
    ((-complexRight c : ℝ) : ℂ) + ((-complexHeight c : ℝ) : ℂ) * Complex.I = (c : ℂ) * rho .one := by
  rw [saddle_one_coordinates]
  simp [complexRight, complexHeight, sub_eq_add_neg, neg_div]

theorem upper_saddle_coordinates (c : ℝ) :
    ((-complexRight c : ℝ) : ℂ) + (complexHeight c : ℂ) * Complex.I = (c : ℂ) * rho .two := by
  rw [saddle_two_coordinates]
  simp [complexRight, complexHeight, neg_div]

theorem horizontal_one_at_lower_saddle {c : ℝ} (hc : 0 < c) :
    horizontalPhase .one c (-complexHeight c) (-complexRight c) = 3 * c / 2 := by
  rw [horizontalPhase, lower_saddle_coordinates, limitingPhase_one_saddle_re hc]

theorem horizontal_one_at_upper_saddle {c : ℝ} (hc : 0 < c) :
    horizontalPhase .one c (complexHeight c) (-complexRight c) =
      3 * c / 2 - 2 * Real.pi * Real.sqrt 3 * c := by
  rw [horizontalPhase, upper_saddle_coordinates, limitingPhase_one_at_two_re hc]

/-- The explicit polygonal Hankel contour has a unique real-phase maximum at
the first limiting saddle. Thus the limiting Neuschel positivity condition holds
on the entire contour, not merely near the saddle. -/
theorem hankel_phase_gap_one {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ hankelTrace (complexRight c) (complexHeight c))
    (hne : s ≠ (c : ℂ) * rho .one) :
    (limitingPhase .one c s).re < 3 * c / 2 := by
  have hR := complexRight_pos hc
  have hH := complexHeight_pos hc
  have hcircle := complexRight_sq_add_height_sq c
  have hcircleNeg : complexRight c ^ 2 + (-complexHeight c) ^ 2 = c ^ 2 := by
    simpa only [neg_sq] using hcircle
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · have hxne : x ≠ -complexRight c := by
      intro he
      exact hne (he ▸ lower_saddle_coordinates c)
    have h := horizontalPhase_strict_max .one hc (neg_ne_zero.mpr hH.ne') hR hcircleNeg hx hxne
    change horizontalPhase .one c (-complexHeight c) x < 3 * c / 2
    simpa only [horizontal_one_at_lower_saddle hc] using h
  · have hv := (verticalPhase_one_strictAnti hc hR).antitone hy.1
    have hb := horizontalPhase_strict_max .one hc (neg_ne_zero.mpr hH.ne') hR hcircleNeg
      (le_refl (complexRight c)) (show complexRight c ≠ -complexRight c by linarith)
    have hb' : verticalPhase .one c (complexRight c) (-complexHeight c) < 3 * c / 2 := by
      change horizontalPhase .one c (-complexHeight c) (complexRight c) < 3 * c / 2
      simpa only [horizontal_one_at_lower_saddle hc] using hb
    exact hv.trans_lt hb'
  · have hu := horizontalPhase_le_max .one hc hH.ne' hR hcircle hx
    have hu' : horizontalPhase .one c (complexHeight c) (-complexRight c) < 3 * c / 2 := by
      rw [horizontal_one_at_upper_saddle hc]
      have hp := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
      nlinarith [mul_pos hp hc]
    exact hu.trans_lt hu'

theorem horizontal_two_at_upper_saddle {c : ℝ} (hc : 0 < c) :
    horizontalPhase .two c (complexHeight c) (-complexRight c) = 3 * c / 2 := by
  rw [horizontalPhase, upper_saddle_coordinates, limitingPhase_two_saddle_re hc]

theorem horizontal_two_at_lower_saddle {c : ℝ} (hc : 0 < c) :
    horizontalPhase .two c (-complexHeight c) (-complexRight c) =
      3 * c / 2 - 2 * Real.pi * Real.sqrt 3 * c := by
  rw [horizontalPhase, lower_saddle_coordinates, limitingPhase_two_at_one_re hc]

theorem hankel_phase_gap_two {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ hankelTrace (complexRight c) (complexHeight c))
    (hne : s ≠ (c : ℂ) * rho .two) :
    (limitingPhase .two c s).re < 3 * c / 2 := by
  have hR := complexRight_pos hc
  have hH := complexHeight_pos hc
  have hcircle := complexRight_sq_add_height_sq c
  have hcircleNeg : complexRight c ^ 2 + (-complexHeight c) ^ 2 = c ^ 2 := by
    simpa only [neg_sq] using hcircle
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · have hu := horizontalPhase_le_max .two hc (neg_ne_zero.mpr hH.ne') hR hcircleNeg hx
    have hu' : horizontalPhase .two c (-complexHeight c) (-complexRight c) < 3 * c / 2 := by
      rw [horizontal_two_at_lower_saddle hc]
      have hp := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
      nlinarith [mul_pos hp hc]
    exact hu.trans_lt hu'
  · have hv := (verticalPhase_two_strictMono hc hR).monotone hy.2
    have hb := horizontalPhase_strict_max .two hc hH.ne' hR hcircle
      (le_refl (complexRight c)) (show complexRight c ≠ -complexRight c by linarith)
    have hb' : verticalPhase .two c (complexRight c) (complexHeight c) < 3 * c / 2 := by
      change horizontalPhase .two c (complexHeight c) (complexRight c) < 3 * c / 2
      simpa only [horizontal_two_at_upper_saddle hc] using hb
    exact hv.trans_lt hb'
  · have hxne : x ≠ -complexRight c := by
      intro he
      exact hne (he ▸ upper_saddle_coordinates c)
    have h := horizontalPhase_strict_max .two hc hH.ne' hR hcircle hx hxne
    change horizontalPhase .two c (complexHeight c) x < 3 * c / 2
    simpa only [horizontal_two_at_upper_saddle hc] using h

theorem vertical_three_at_saddle {c : ℝ} (hc : 0 < c) :
    verticalPhase .three c c 0 = -3 * c := by
  simpa [verticalPhase] using limitingPhase_three_saddle_re hc

theorem hankel_phase_gap_three {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ hankelTrace c c) (hne : s ≠ (c : ℂ) * rho .three) :
    (limitingPhase .three c s).re < -3 * c := by
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · have hh : c ^ 2 ≤ (-c) ^ 2 := by simp
    have h := horizontalPhase_monotone_large_height .three hc (neg_ne_zero.mpr hc.ne') hh hx
    have hv := verticalPhase_three_strict_max hc hc (neg_ne_zero.mpr hc.ne')
    rw [vertical_three_at_saddle hc] at hv
    exact h.trans_lt hv
  · have hy0 : y ≠ 0 := by
      intro he
      apply hne
      simp [he]
    have hv := verticalPhase_three_strict_max hc hc hy0
    rwa [vertical_three_at_saddle hc] at hv
  · have h := horizontalPhase_monotone_large_height .three hc hc.ne' (le_refl (c ^ 2)) hx
    have hv := verticalPhase_three_strict_max hc hc hc.ne'
    rw [vertical_three_at_saddle hc] at hv
    exact h.trans_lt hv

theorem hankelTrace_mem_slitPlane {right height : ℝ} (hr : 0 < right) (hh : 0 < height)
    {s : ℂ} (hs : s ∈ hankelTrace right height) : s ∈ Complex.slitPlane := by
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using neg_ne_zero.mpr hh.ne'
  · apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using hr
  · apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using hh.ne'

theorem hankelTrace_re_le {right height : ℝ} {s : ℂ} (hs : s ∈ hankelTrace right height) :
    s.re ≤ right := by
  rcases hs with (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩
  · simpa using hx
  · simp
  · simpa using hx

end ThisWork
