module

public import ThisWork.Argument
public import ThisWork.RemainderPieces

/-! Exact finite-remainder sums and their uniform exponential estimate. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory
open scoped Topology

theorem continuousOn_lower_of_continuousTrace {r h : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (hankelTrace r h)) :
    ContinuousOn (fun u : ℝ => f ((u : ℂ) - (h : ℂ) * Complex.I)) (Iic r) := by
  apply hf.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) - (h : ℂ) * Complex.I)).continuousOn
  intro u hu
  exact Or.inl (Or.inl ⟨u, hu, by simp [sub_eq_add_neg]⟩)

theorem continuousOn_upper_of_continuousTrace {r h : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (hankelTrace r h)) :
    ContinuousOn (fun u : ℝ => f ((u : ℂ) + (h : ℂ) * Complex.I)) (Iic r) := by
  apply hf.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + (h : ℂ) * Complex.I)).continuousOn
  intro u hu
  exact Or.inr ⟨u, hu, rfl⟩

theorem intervalIntegrable_lower_of_continuousTrace {r h a b : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (hankelTrace r h)) (ha : a ≤ r) (hb : b ≤ r) :
    IntervalIntegrable (fun u : ℝ => f ((u : ℂ) - (h : ℂ) * Complex.I)) volume a b := by
  exact ((continuousOn_lower_of_continuousTrace hf).mono
    (fun _ hu => hu.2.trans (max_le ha hb))).intervalIntegrable

theorem intervalIntegrable_upper_of_continuousTrace {r h a b : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (hankelTrace r h)) (ha : a ≤ r) (hb : b ≤ r) :
    IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (h : ℂ) * Complex.I)) volume a b := by
  exact ((continuousOn_upper_of_continuousTrace hf).mono
    (fun _ hu => hu.2.trans (max_le ha hb))).intervalIntegrable

theorem intervalIntegrable_vertical_of_continuousTrace {r h a b : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f (hankelTrace r h)) (ha : a ∈ Icc (-h) h) (hb : b ∈ Icc (-h) h) :
    IntervalIntegrable (fun v : ℝ => Complex.I * f ((r : ℂ) + (v : ℂ) * Complex.I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.mul
  apply hf.comp (by fun_prop : Continuous (fun v : ℝ => (r : ℂ) + (v : ℂ) * Complex.I)).continuousOn
  intro v hv
  exact Or.inl (Or.inr ⟨v, ⟨(le_min ha.1 hb.1).trans hv.1, hv.2.trans (max_le ha.2 hb.2)⟩, rfl⟩)

theorem finiteHankel_sub_window_eq_sum {c a b T : ℝ} (hc : 0 < c) (hT : 2 * c ≤ T)
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : a < c / 16) (hb : b < c / 16)
    (j : Branch) {σ : ℂ} (hσ : σ ∈ saddleDisk c j) {f : ℂ → ℂ}
    (hf : ContinuousOn f (hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ))) :
    finiteHankelIntegral (-T) (saddleContourRight c j σ) (saddleContourHeight c j σ) f -
      contourWindow j σ a b (saddleContourRight c j σ) (saddleContourHeight c j σ) f =
      ∑ i : Fin 4, (remainderPieces c j σ a b T i).integral
        (saddleContourRight c j σ) (saddleContourHeight c j σ) f := by
  have he := saddleWindow_endpoint_bounds hc hT ha hb j hσ
  cases j
  · change -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2 at he
    have hl : σ.re - a ≤ saddleContourRight c .one σ := by change σ.re - a ≤ c / 2; linarith [he.2]
    have hu : σ.re + b ≤ saddleContourRight c .one σ := he.2
    have hT' : -T ≤ saddleContourRight c .one σ := by change -T ≤ c / 2; linarith
    have hd := finiteHankelIntegral_sub_lower_window
      (intervalIntegrable_lower_of_continuousTrace hf hT' hl)
      (intervalIntegrable_lower_of_continuousTrace hf hl hu)
      (intervalIntegrable_lower_of_continuousTrace hf hu le_rfl)
    simpa [remainderPieces, SaddleRemainderPiece.integral, SaddleContourEdge.velocity,
      SaddleContourEdge.point, Fin.sum_univ_succ, saddleContourRight, saddleContourHeight,
      sub_eq_add_neg, add_assoc] using hd
  · change -T ≤ σ.re - a ∧ σ.re + b ≤ c / 2 at he
    have hl : σ.re - a ≤ saddleContourRight c .two σ := by change σ.re - a ≤ c / 2; linarith [he.2]
    have hu : σ.re + b ≤ saddleContourRight c .two σ := he.2
    have hT' : -T ≤ saddleContourRight c .two σ := by change -T ≤ c / 2; linarith
    have hd := finiteHankelIntegral_sub_upper_window
      (intervalIntegrable_upper_of_continuousTrace hf hT' hl)
      (intervalIntegrable_upper_of_continuousTrace hf hl hu)
      (intervalIntegrable_upper_of_continuousTrace hf hu le_rfl)
    simpa [remainderPieces, SaddleRemainderPiece.integral, SaddleContourEdge.velocity,
      SaddleContourEdge.point, Fin.sum_univ_succ, saddleContourRight, saddleContourHeight,
      sub_eq_add_neg, add_assoc] using hd
  · change -c ≤ σ.im - a ∧ σ.im + b ≤ c at he
    have hl : σ.im - a ∈ Icc (-saddleContourHeight c .three σ) (saddleContourHeight c .three σ) :=
      ⟨he.1, by change σ.im - a ≤ c; linarith [he.2]⟩
    have hu : σ.im + b ∈ Icc (-saddleContourHeight c .three σ) (saddleContourHeight c .three σ) :=
      ⟨by change -c ≤ σ.im + b; linarith [he.1], he.2⟩
    have hbott : -saddleContourHeight c .three σ ∈
        Icc (-saddleContourHeight c .three σ) (saddleContourHeight c .three σ) :=
      ⟨le_rfl, by change -c ≤ c; linarith⟩
    have htop : saddleContourHeight c .three σ ∈
        Icc (-saddleContourHeight c .three σ) (saddleContourHeight c .three σ) :=
      ⟨by change -c ≤ c; linarith, le_rfl⟩
    have hd := finiteHankelIntegral_sub_vertical_window (left := -T)
      (intervalIntegrable_vertical_of_continuousTrace hf hbott hl)
      (intervalIntegrable_vertical_of_continuousTrace hf hl hu)
      (intervalIntegrable_vertical_of_continuousTrace hf hu htop)
    simpa [remainderPieces, SaddleRemainderPiece.integral, SaddleContourEdge.velocity,
      SaddleContourEdge.point, Fin.sum_univ_succ, saddleContourRight, saddleContourHeight,
      sub_eq_add_neg, add_assoc] using hd

theorem scaled_hankelTrace_mem_kernelDomain {α₁ α₂ R r h : ℝ} (n : ℕ)
    (hR : 0 < R) (hr : 0 < r) (hh : 0 < h)
    (hright : R * r < min (α₁ * n + 1) (α₂ * n + 1)) {s : ℂ}
    (hs : s ∈ hankelTrace r h) : (R : ℂ) * s ∈ kernelDomain α₁ α₂ n := by
  change _ ∈ Complex.slitPlane ∧ _ < min (α₁ * n + 1) (α₂ * n + 1)
  refine ⟨hankelTrace_mem_slitPlane (mul_pos hR hr) (mul_pos hR hh) (hankelTrace_scale hR.le hs), ?_⟩
  have hre : s.re ≤ r := by
    rcases mem_hankelTrace_iff.mp hs with (⟨hre, _⟩ | ⟨hre, _, _⟩) | ⟨hre, _⟩
    · exact hre
    · exact hre.le
    · exact hre
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    (mul_le_mul_of_nonneg_left hre hR.le).trans_lt hright

theorem eventually_continuousOn_moment_kernel_contour [PositiveArgument] {α₁ α₂ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (j : Branch) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ContinuousOn (fun s => s ^ k * normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s))
        (hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)) := by
  filter_upwards [eventually_saddleContours_admissible h₁ h₂ j] with n hn σ hσ
  have ha := hn.2 σ hσ
  have hc := saddleScale_pos h₁ h₂
  have hr := saddleContourRight_bounds hc j hσ
  have hh := saddleContourHeight_bounds hc j hσ
  have hh0 : 0 < saddleContourHeight (saddleScale α₁ α₂) j σ := by linarith
  have hk := (differentiableOn_kernel α₁ α₂ j n).continuousOn.comp
    (s := hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
      (saddleContourHeight (saddleScale α₁ α₂) j σ))
    (by fun_prop : Continuous (fun s : ℂ => (largeScale n : ℂ) * s)).continuousOn
    (fun s hs => scaled_hankelTrace_mem_kernelDomain n (largeScale_pos hn.1) hr.1 hh0 ha.2.1 hs)
  exact (continuous_id.pow k).continuousOn.mul hk

theorem uniform_finite_window_remainder_bound [PositiveArgument] {α₁ α₂ a b T : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (ha0 : 0 < a) (hb0 : 0 < b)
    (hT : 2 * saddleScale α₁ α₂ ≤ T)
    (ha : a < saddleScale α₁ α₂ / 16) (hb : b < saddleScale α₁ α₂ / 16)
    (j : Branch) (D : ℝ) (k : ℕ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ saddleDisk (saddleScale α₁ α₂) j,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ‖finiteHankelIntegral (-T) (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)
          (fun s => s ^ k * normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s)) -
        contourWindow j σ a b (saddleContourRight (saddleScale α₁ α₂) j σ)
          (saddleContourHeight (saddleScale α₁ α₂) j σ)
          (fun s => s ^ k * normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * s))‖ ≤
        4 * ((T + 4 * saddleScale α₁ α₂) ^ k *
          ‖normalizedKernel α₁ α₂ j n ((largeScale n : ℂ) * σ)‖ * Real.exp (-ε * largeScale n)) *
          (2 * T + 8 * saddleScale α₁ α₂) := by
  obtain ⟨ε, hε, hbnd⟩ := uniform_moment_remainderPiece_bound h₁ h₂ ha0 hb0 hT ha hb j D k
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbnd, eventually_continuousOn_moment_kernel_contour h₁ h₂ j k]
    with n hn hcont σ hσ hdisp
  rw [finiteHankel_sub_window_eq_sum (saddleScale_pos h₁ h₂) hT ha0 hb0 ha hb j hσ (hcont σ hσ)]
  have hsum := (norm_sum_le Finset.univ _).trans
    (Finset.sum_le_sum (fun (i : Fin 4) _ => hn σ hσ hdisp i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using hsum

end ThisWork.Analytic
