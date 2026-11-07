module

public import ThisWork.Argument
public import ThisWork.WindowRemainderGeometry

/-! The four finite oriented pieces left after extracting each saddle window. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory
open scoped Topology

inductive SaddleContourEdge where
  | lower | vertical | upper
  deriving DecidableEq

noncomputable def SaddleContourEdge.velocity : SaddleContourEdge → ℂ
  | .lower => 1
  | .vertical => Complex.I
  | .upper => -1

noncomputable def SaddleContourEdge.point (r h : ℝ) : SaddleContourEdge → ℝ → ℂ
  | .lower => fun t => (t : ℂ) - (h : ℂ) * Complex.I
  | .vertical => fun t => (r : ℂ) + (t : ℂ) * Complex.I
  | .upper => fun t => (t : ℂ) + (h : ℂ) * Complex.I

@[simp] theorem SaddleContourEdge.norm_velocity (e : SaddleContourEdge) : ‖e.velocity‖ = 1 := by
  cases e <;> simp [velocity]

structure SaddleRemainderPiece where
  edge : SaddleContourEdge
  lower : ℝ
  upper : ℝ

noncomputable def remainderPieces (c : ℝ) (j : Branch) (σ : ℂ) (a b T : ℝ) : Fin 4 → SaddleRemainderPiece :=
  let r := saddleContourRight c j σ
  let h := saddleContourHeight c j σ
  match j with
  | .one => ![⟨.lower, -T, σ.re - a⟩, ⟨.lower, σ.re + b, r⟩,
      ⟨.vertical, -h, h⟩, ⟨.upper, -T, r⟩]
  | .two => ![⟨.lower, -T, r⟩, ⟨.vertical, -h, h⟩,
      ⟨.upper, -T, σ.re - a⟩, ⟨.upper, σ.re + b, r⟩]
  | .three => ![⟨.lower, -T, r⟩, ⟨.vertical, -h, σ.im - a⟩,
      ⟨.vertical, σ.im + b, h⟩, ⟨.upper, -T, r⟩]

theorem saddleWindow_endpoint_bounds {c a b T : ℝ} (hc : 0 < c) (hT : 2 * c ≤ T)
    (ha : a < c / 16) (hb : b < c / 16) (j : Branch) {σ : ℂ}
    (hσ : σ ∈ saddleDisk c j) :
    match j with
    | .one | .two => -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2
    | .three => -c ≤ σ.im - a ∧ σ.im + b ≤ c := by
  have hnorm := saddleDisk_norm_le hc j hσ
  have hre := (Complex.abs_re_le_norm σ).trans hnorm
  have hside := saddleDisk_im_side hc j hσ
  have hregion := saddleDisk_region hc j hσ
  cases j
  · change σ.re ≤ -(c / 4) ∧ _ at hregion
    constructor <;> linarith [(abs_le.mp hre).1, hregion.1]
  · change σ.re ≤ -(c / 4) ∧ _ at hregion
    constructor <;> linarith [(abs_le.mp hre).1, hregion.1]
  · change |σ.im| ≤ c / 4 at hside
    constructor <;> linarith [(abs_le.mp hside).1, (abs_le.mp hside).2]

theorem remainderPieces_ordered {c a b T : ℝ} (hc : 0 < c) (hT : 2 * c ≤ T)
    (ha : a < c / 16) (hb : b < c / 16) (j : Branch) {σ : ℂ}
    (hσ : σ ∈ saddleDisk c j) (i : Fin 4) :
    (remainderPieces c j σ a b T i).lower ≤ (remainderPieces c j σ a b T i).upper := by
  have he := saddleWindow_endpoint_bounds hc hT ha hb j hσ
  have hregion := saddleDisk_region hc j hσ
  cases j
  · change -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2 at he
    fin_cases i <;> simp [remainderPieces, saddleContourRight, saddleContourHeight]
    all_goals linarith [he.1, he.2, abs_nonneg σ.im]
  · change -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2 at he
    fin_cases i <;> simp [remainderPieces, saddleContourRight, saddleContourHeight]
    all_goals linarith [he.1, he.2, abs_nonneg σ.im]
  · change -c ≤ σ.im - a ∧ σ.im + b ≤ c at he
    change c / 2 ≤ σ.re at hregion
    fin_cases i <;> simp [remainderPieces, saddleContourRight, saddleContourHeight]
    all_goals linarith [he.1, he.2]

theorem remainderPieces_geometry {c a b T : ℝ} (hc : 0 < c) (hT : 2 * c ≤ T)
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : a < c / 16) (hb : b < c / 16)
    (j : Branch) {σ : ℂ} (hσ : σ ∈ saddleDisk c j) (i : Fin 4) {t : ℝ}
    (ht : t ∈ uIcc (remainderPieces c j σ a b T i).lower (remainderPieces c j σ a b T i).upper) :
    let s := (remainderPieces c j σ a b T i).edge.point
      (saddleContourRight c j σ) (saddleContourHeight c j σ) t
    s ∈ hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ) ∧
      -T ≤ s.re ∧ OutsideSaddleWindow j σ a b s := by
  rw [uIcc_of_le (remainderPieces_ordered hc hT ha hb j hσ i)] at ht
  have hside := saddleDisk_im_side hc j hσ
  have hregion := saddleDisk_region hc j hσ
  have he := saddleWindow_endpoint_bounds hc hT ha hb j hσ
  have hlo (u : ℝ) (hl : -T ≤ u) (hr : u ≤ saddleContourRight c j σ) :
      (u : ℂ) - (saddleContourHeight c j σ : ℂ) * Complex.I ∈
        hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ) ∧
      -T ≤ ((u : ℂ) - (saddleContourHeight c j σ : ℂ) * Complex.I).re := by
    exact ⟨Or.inl (Or.inl ⟨u, hr, by simp [sub_eq_add_neg]⟩), by simpa [Complex.mul_re] using hl⟩
  have hhi (u : ℝ) (hl : -T ≤ u) (hr : u ≤ saddleContourRight c j σ) :
      (u : ℂ) + (saddleContourHeight c j σ : ℂ) * Complex.I ∈
        hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ) ∧
      -T ≤ ((u : ℂ) + (saddleContourHeight c j σ : ℂ) * Complex.I).re := by
    exact ⟨Or.inr ⟨u, hr, rfl⟩, by simpa [Complex.mul_re] using hl⟩
  have hv (u : ℝ) (hu : u ∈ Icc (-saddleContourHeight c j σ) (saddleContourHeight c j σ)) :
      (saddleContourRight c j σ : ℂ) + (u : ℂ) * Complex.I ∈
        hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ) ∧
      -T ≤ ((saddleContourRight c j σ : ℂ) + (u : ℂ) * Complex.I).re := by
    refine ⟨Or.inl (Or.inr ⟨u, hu, rfl⟩), ?_⟩
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith [(saddleContourRight_bounds hc j hσ).1]
  cases j
  · change σ.im ≤ -(c / 4) at hside
    change σ.re ≤ -(c / 4) ∧ _ at hregion
    change -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2 at he
    fin_cases i
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hlo t ht.1 (by change t ≤ c / 2; linarith [ht.2, hregion.1])
      refine ⟨hx.1, hx.2, ?_⟩
      right; left
      simpa [Complex.mul_re] using ht.2
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hlo t (by linarith [ht.1, he.1]) ht.2
      refine ⟨hx.1, hx.2, ?_⟩
      right; right
      simpa [Complex.mul_re] using ht.1
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hv t ht
      refine ⟨hx.1, hx.2, ?_⟩
      right; right
      simpa [Complex.mul_re] using he.2
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hhi t ht.1 ht.2
      refine ⟨hx.1, hx.2, ?_⟩
      left
      have hn : |σ.im| ≠ σ.im := by rw [abs_of_nonpos (show σ.im ≤ 0 by linarith)]; linarith
      simpa [Complex.mul_im] using hn
  · change c / 4 ≤ σ.im at hside
    change σ.re ≤ -(c / 4) ∧ _ at hregion
    change -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2 at he
    fin_cases i
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hlo t ht.1 ht.2
      refine ⟨hx.1, hx.2, ?_⟩
      left
      have hn : -|σ.im| ≠ σ.im := by rw [abs_of_nonneg (show 0 ≤ σ.im by linarith)]; linarith
      simpa [Complex.mul_im] using hn
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hv t ht
      refine ⟨hx.1, hx.2, ?_⟩
      right; right
      simpa [Complex.mul_re] using he.2
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hhi t ht.1 (by change t ≤ c / 2; linarith [ht.2, hregion.1])
      refine ⟨hx.1, hx.2, ?_⟩
      right; left
      simpa [Complex.mul_re] using ht.2
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hhi t (by linarith [ht.1, he.1]) ht.2
      refine ⟨hx.1, hx.2, ?_⟩
      right; right
      simpa [Complex.mul_re] using ht.1
  · change |σ.im| ≤ c / 4 at hside
    change c / 2 ≤ σ.re at hregion
    change -c ≤ σ.im - a ∧ σ.im + b ≤ c at he
    fin_cases i
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hlo t ht.1 ht.2
      refine ⟨hx.1, hx.2, ?_⟩
      right; left
      simpa [Complex.mul_im] using he.1
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hv t ⟨ht.1, by change t ≤ c; linarith [ht.2, he.2]⟩
      refine ⟨hx.1, hx.2, ?_⟩
      right; left
      simpa [Complex.mul_im] using ht.2
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hv t ⟨by change -c ≤ t; linarith [ht.1, he.1], ht.2⟩
      refine ⟨hx.1, hx.2, ?_⟩
      right; right
      simpa [Complex.mul_im] using ht.1
    · simp [remainderPieces, saddleContourRight, saddleContourHeight] at ht
      dsimp [remainderPieces, SaddleContourEdge.point, saddleContourRight, saddleContourHeight]
      have hx := hhi t ht.1 ht.2
      refine ⟨hx.1, hx.2, ?_⟩
      right; right
      simpa [Complex.mul_im] using he.2

theorem remainderPieces_length_le {c a b T : ℝ} (hc : 0 < c) (hT : 2 * c ≤ T)
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : a < c / 16) (hb : b < c / 16)
    (j : Branch) {σ : ℂ} (hσ : σ ∈ saddleDisk c j) (i : Fin 4) :
    |(remainderPieces c j σ a b T i).upper - (remainderPieces c j σ a b T i).lower| ≤ 2 * T + 8 * c := by
  rw [abs_of_nonneg (sub_nonneg.mpr (remainderPieces_ordered hc hT ha hb j hσ i))]
  have hnorm := saddleDisk_norm_le hc j hσ
  have hre := (Complex.abs_re_le_norm σ).trans hnorm
  have him := (Complex.abs_im_le_norm σ).trans hnorm
  cases j <;> fin_cases i <;> simp [remainderPieces, saddleContourRight, saddleContourHeight]
  all_goals linarith [(abs_le.mp hre).1, (abs_le.mp hre).2, (abs_le.mp him).1, (abs_le.mp him).2]

noncomputable def SaddleRemainderPiece.integral (p : SaddleRemainderPiece) (r h : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ t in p.lower..p.upper, p.edge.velocity * f (p.edge.point r h t)

theorem uniform_moment_remainderPiece_bound [PositiveArgument] {α₁ α₂ a b T : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (ha0 : 0 < a) (hb0 : 0 < b)
    (hT : 2 * saddleScale α₁ α₂ ≤ T)
    (ha : a < saddleScale α₁ α₂ / 16) (hb : b < saddleScale α₁ α₂ / 16)
    (j : Branch) (D : ℝ) (k : ℕ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n → ∀ i : Fin 4,
      ‖(remainderPieces (saddleScale α₁ α₂) j σ a b T i).integral
        (saddleContourRight (saddleScale α₁ α₂) j σ) (saddleContourHeight (saddleScale α₁ α₂) j σ)
        (fun s => s ^ k * normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s))‖ ≤
      ((T + 4 * saddleScale α₁ α₂) ^ k * ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ *
        Real.exp (-ε * largeScale n)) * (2 * T + 8 * saddleScale α₁ α₂) := by
  have hc := saddleScale_pos h₁ h₂
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨ε, hε, hbnd⟩ := uniform_moment_window_remainder_piece h₁ h₂ ha0 hb0 hT0 ha hb j D k
  refine ⟨ε, hε, hbnd.mono (fun n hn σ hσ hdisp i => ?_)⟩
  let p := remainderPieces (saddleScale α₁ α₂) j σ a b T i
  have hp := hn σ hσ hdisp p.lower p.upper p.edge.velocity
    (p.edge.point (saddleContourRight (saddleScale α₁ α₂) j σ)
      (saddleContourHeight (saddleScale α₁ α₂) j σ))
    (fun t ht => remainderPieces_geometry hc hT ha0 hb0 ha hb j hσ i ht)
  simp only [SaddleContourEdge.norm_velocity, one_mul] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (remainderPieces_length_le hc hT ha0 hb0 ha hb j hσ i) (by positivity))

end ThisWork.Analytic
