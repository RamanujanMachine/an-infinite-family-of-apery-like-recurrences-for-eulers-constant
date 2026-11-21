module

public import ThisWork.Trajectory.CanonicalTails
public import ThisWork.FullWindowRemainder

/-! Uniform remainder bounds outside the canonical saddle window. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric MeasureTheory Analytic
open scoped Topology

theorem eventually_continuousOn_canonical_moment_contour {A₁ A₂ z c : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hc : 0 < c) (m d k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk c .three,
      ContinuousOn (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))
        (hankelTrace (saddleContourRight c .three σ) (saddleContourHeight c .three σ)) := by
  filter_upwards [eventually_right_factor_conditions h₁ (5 * c / 4),
    eventually_right_factor_conditions h₂ (5 * c / 4), eventually_gt_atTop (0 : ℕ)]
    with n hA₁ hA₂ hn σ hσ
  have hr : 0 < σ.re := by have h := saddleDisk_region hc .three hσ; change c / 2 ≤ σ.re at h; linarith
  have hupper : sqrtScale n * σ.re < min (A₁ * n + 1) (A₂ * n + 1) := by
    have hb := mul_le_mul_of_nonneg_left ((Complex.re_le_norm σ).trans (saddleDisk_norm_le hc .three hσ))
      (sqrtScale_pos hn).le
    exact lt_min (by linarith [hA₁.1, hA₁.2]) (by linarith [hA₂.1, hA₂.2])
  have hK := (differentiableOn_kernel hz m d A₁ A₂ .three n).continuousOn.comp
    (s := hankelTrace (saddleContourRight c .three σ) (saddleContourHeight c .three σ))
    (by fun_prop : Continuous (fun s : ℂ => (sqrtScale n : ℂ) * s)).continuousOn
    (fun s hs => scaled_hankelTrace_mem_kernelDomain n (sqrtScale_pos hn) hr hc hupper hs)
  exact (continuous_id.pow k).continuousOn.mul hK

theorem uniform_canonical_remainderPiece_bound {d : ℕ} {A₁ A₂ z a b T : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (ha₀ : 0 < a) (hb₀ : 0 < b) (hT : 2 * doubleSaddleScale d A₁ A₂ z ≤ T)
    (ha : a < doubleSaddleScale d A₁ A₂ z / 16) (hb : b < doubleSaddleScale d A₁ A₂ z / 16)
    (m k : ℕ) (D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n → ∀ i : Fin 4,
      ‖(remainderPieces (doubleSaddleScale d A₁ A₂ z) .three σ a b T i).integral
        (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
        (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
        (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))‖ ≤
      ((T + 4 * doubleSaddleScale d A₁ A₂ z) ^ k *
        ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n)) *
        (2 * T + 8 * doubleSaddleScale d A₁ A₂ z) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  have hT₀ : 0 ≤ T := by linarith
  obtain ⟨ε, hε, hgap⟩ := uniform_kernel_compact_gap hd h₁ h₂ hz (lt_min ha₀ hb₀) m (T + 4 * c) D
  refine ⟨ε, hε, hgap.mono (fun n hn σ hσ hdisp i => ?_)⟩
  let p := remainderPieces c .three σ a b T i
  have hbound : ∀ t ∈ uIoc p.lower p.upper,
      ‖p.edge.velocity * ((p.edge.point (saddleContourRight c .three σ) (saddleContourHeight c .three σ) t) ^ k *
        kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) *
          p.edge.point (saddleContourRight c .three σ) (saddleContourHeight c .three σ) t))‖ ≤
      (T + 4 * c) ^ k * ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n) := by
    intro t ht
    have hg := remainderPieces_geometry hc hT ha₀ hb₀ ha hb .three hσ i (uIoc_subset_uIcc ht)
    have hnorm := bounded_saddleContour_norm hc (by linarith : 0 ≤ T) .three hσ hg.1 hg.2.1
    have hK := hn σ hσ hdisp _ hg.1 hnorm (contour_gap_outside_window hc ha hb .three hσ hg.1 hg.2.2)
    rw [norm_mul, SaddleContourEdge.norm_velocity, one_mul, norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm k) hK (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  exact hInt.trans (mul_le_mul_of_nonneg_left
    (remainderPieces_length_le hc hT ha₀ hb₀ ha hb .three hσ i) (by positivity))

theorem uniform_finite_canonical_window_remainder {d : ℕ} {A₁ A₂ z a b T : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (ha₀ : 0 < a) (hb₀ : 0 < b) (hT : 2 * doubleSaddleScale d A₁ A₂ z ≤ T)
    (ha : a < doubleSaddleScale d A₁ A₂ z / 16) (hb : b < doubleSaddleScale d A₁ A₂ z / 16)
    (m k : ℕ) (D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      ‖finiteHankelIntegral (-T) (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)) -
        contourWindow .three σ a b (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))‖ ≤
        4 * ((T + 4 * doubleSaddleScale d A₁ A₂ z) ^ k *
          ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n)) *
          (2 * T + 8 * doubleSaddleScale d A₁ A₂ z) := by
  obtain ⟨ε, hε, hbnd⟩ := uniform_canonical_remainderPiece_bound hd h₁ h₂ hz ha₀ hb₀ hT ha hb m k D
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbnd, eventually_continuousOn_canonical_moment_contour h₁ h₂ hz
    (doubleSaddleScale_pos hd h₁ h₂ hz) m d k] with n hn hcont σ hσ hdisp
  rw [finiteHankel_sub_window_eq_sum (doubleSaddleScale_pos hd h₁ h₂ hz) hT ha₀ hb₀ ha hb .three hσ (hcont σ hσ)]
  have hsum := (norm_sum_le Finset.univ _).trans
    (Finset.sum_le_sum (fun (i : Fin 4) _ => hn σ hσ hdisp i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using hsum

theorem uniform_canonical_hankel_truncation {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (m k : ℕ) (D : ℝ) :
    ∃ T ≥ 1, 2 * doubleSaddleScale d A₁ A₂ z ≤ T ∧ ∃ ε > 0, ∃ B ≥ 0,
      ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      ‖hankelIntegral (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)) -
        finiteHankelIntegral (-T) (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))‖ ≤
        B * ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨T, hT₁, hTc, ε, hε, B, hB, hbnd⟩ := uniform_integrated_canonical_tail hd h₁ h₂ hz m k D
  refine ⟨T, hT₁, hTc, ε, hε, 2 * B, by positivity, ?_⟩
  filter_upwards [hbnd, eventually_continuousOn_canonical_moment_contour h₁ h₂ hz hc m d k]
    with n hn hcont σ hσ hdisp
  have hu := hn σ hσ hdisp c (abs_of_pos hc)
  have hl := hn σ hσ hdisp (-c) (by rw [abs_neg, abs_of_pos hc])
  let r := saddleContourRight c .three σ
  let h := saddleContourHeight c .three σ
  let f : ℂ → ℂ := fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)
  have hct : ContinuousOn f (hankelTrace r h) := hcont σ hσ
  have hel : (fun u : ℝ => f (((-u : ℝ) : ℂ) - (h : ℂ) * Complex.I)) =
      leftMomentKernel m d A₁ A₂ z .three n k (-c) := by
    funext u
    dsimp only [f, h, saddleContourHeight, leftMomentKernel]
    simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]
  have heu : (fun u : ℝ => f (((-u : ℝ) : ℂ) + (h : ℂ) * Complex.I)) =
      leftMomentKernel m d A₁ A₂ z .three n k c := by
    funext u
    dsimp only [f, h, saddleContourHeight, leftMomentKernel]
    simp only [Complex.ofReal_neg]
  have hli : IntegrableOn (fun u : ℝ => f (((-u : ℝ) : ℂ) - (h : ℂ) * Complex.I)) (Ioi T) := by
    rw [hel]
    exact hl.1
  have hui : IntegrableOn (fun u : ℝ => f (((-u : ℝ) : ℂ) + (h : ℂ) * Complex.I)) (Ioi T) := by
    rw [heu]
    exact hu.1
  have il := integrableOn_Iic_of_reflected_tail (continuousOn_lower_of_continuousTrace hct) hli
  have iu := integrableOn_Iic_of_reflected_tail (continuousOn_upper_of_continuousTrace hct) hui
  have hnl := hl.2
  have hnu := hu.2
  rw [← hel, integral_comp_neg_Ioi T (fun u : ℝ => f ((u : ℂ) - (h : ℂ) * Complex.I))] at hnl
  rw [← heu, integral_comp_neg_Ioi T (fun u : ℝ => f ((u : ℂ) + (h : ℂ) * Complex.I))] at hnu
  have htrunc := norm_hankelIntegral_sub_truncation
    (left := -T) (by dsimp only [r]; linarith [(saddleContourRight_bounds hc .three hσ).1]) il iu
  exact htrunc.trans (by linarith)

/-- The complete canonical Hankel moment differs from its local saddle window
by a uniformly exponentially small quantity. -/
theorem uniform_full_canonical_window_remainder {d : ℕ} {A₁ A₂ z a b : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (ha₀ : 0 < a) (hb₀ : 0 < b)
    (ha : a < doubleSaddleScale d A₁ A₂ z / 16) (hb : b < doubleSaddleScale d A₁ A₂ z / 16)
    (m k : ℕ) (D : ℝ) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three,
      ‖σ - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ D / sqrtScale n →
      ‖hankelIntegral (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s)) -
        contourWindow .three σ a b (saddleContourRight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (saddleContourHeight (doubleSaddleScale d A₁ A₂ z) .three σ)
          (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))‖ ≤
        C * ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖ * Real.exp (-ε * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨T, _, hTc, εt, hεt, Bt, hBt, htail⟩ := uniform_canonical_hankel_truncation hd h₁ h₂ hz m k D
  obtain ⟨εf, hεf, hfinite⟩ := uniform_finite_canonical_window_remainder hd h₁ h₂ hz ha₀ hb₀ hTc ha hb m k D
  let Bf := 4 * (T + 4 * c) ^ k * (2 * T + 8 * c)
  have hT₀ : 0 ≤ T := by linarith
  have hBf : 0 ≤ Bf := by dsimp only [Bf]; positivity
  let q := min εt εf
  refine ⟨q, lt_min hεt hεf, Bt + Bf, add_nonneg hBt hBf, ?_⟩
  filter_upwards [htail, hfinite] with n htn hfn σ hσ hdisp
  have hR : 0 ≤ sqrtScale n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have heT : Real.exp (-εt * sqrtScale n) ≤ Real.exp (-q * sqrtScale n) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left εt εf) hR])
  have heF : Real.exp (-εf * sqrtScale n) ≤ Real.exp (-q * sqrtScale n) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right (min_le_right εt εf) hR])
  let K := ‖kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * σ)‖
  let H := hankelIntegral (saddleContourRight c .three σ) (saddleContourHeight c .three σ)
    (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))
  let F := finiteHankelIntegral (-T) (saddleContourRight c .three σ) (saddleContourHeight c .three σ)
    (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))
  let W := contourWindow .three σ a b (saddleContourRight c .three σ) (saddleContourHeight c .three σ)
    (fun s => s ^ k * kernel m d A₁ A₂ z .three n ((sqrtScale n : ℂ) * s))
  have ht1 : ‖H - F‖ ≤ Bt * K * Real.exp (-q * sqrtScale n) :=
    (htn σ hσ hdisp).trans (mul_le_mul_of_nonneg_left heT (by positivity))
  have hf1 : ‖F - W‖ ≤ Bf * K * Real.exp (-q * sqrtScale n) := by
    calc
      _ ≤ 4 * ((T + 4 * c) ^ k * K * Real.exp (-εf * sqrtScale n)) * (2 * T + 8 * c) := hfn σ hσ hdisp
      _ = Bf * K * Real.exp (-εf * sqrtScale n) := by dsimp only [Bf]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heF (by positivity)
  have htri := norm_add_le (H - F) (F - W)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans ((add_le_add ht1 hf1).trans_eq (by ring))

end ThisWork.Trajectory
