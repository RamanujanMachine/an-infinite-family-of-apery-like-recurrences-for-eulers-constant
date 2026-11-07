module

public import ThisWork.Argument
public import ThisWork.SaddleContours

/-! Uniform limiting phase gaps on bounded contour pieces and their perturbations. -/

public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

theorem mem_hankelTrace_iff {r h : ℝ} {s : ℂ} :
    s ∈ hankelTrace r h ↔
      ((s.re ≤ r ∧ s.im = -h) ∨ (s.re = r ∧ -h ≤ s.im ∧ s.im ≤ h)) ∨
        (s.re ≤ r ∧ s.im = h) := by
  constructor
  · rintro ((⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact Or.inl (Or.inl (by simpa using And.intro hx (rfl : (-h : ℝ) = -h)))
    · exact Or.inl (Or.inr (by simpa using And.intro (rfl : r = r) hy))
    · exact Or.inr (by simpa using And.intro hx (rfl : h = h))
  · rintro ((⟨hr, hi⟩ | ⟨hr, hy⟩) | ⟨hr, hi⟩)
    · exact Or.inl (Or.inl ⟨s.re, hr, by rw [← hi]; exact (Complex.re_add_im s).symm⟩)
    · exact Or.inl (Or.inr ⟨s.im, hy, by rw [← hr]; exact (Complex.re_add_im s).symm⟩)
    · exact Or.inr ⟨s.re, hr, by rw [← hi]; exact (Complex.re_add_im s).symm⟩

theorem continuous_saddleContourRight (c : ℝ) (j : Branch) :
    Continuous (saddleContourRight c j) := by
  cases j
  · exact continuous_const
  · exact continuous_const
  · exact Complex.continuous_re

theorem continuous_saddleContourHeight (c : ℝ) (j : Branch) :
    Continuous (saddleContourHeight c j) := by
  cases j
  · exact Complex.continuous_im.abs
  · exact Complex.continuous_im.abs
  · exact continuous_const

theorem isClosed_hankelTrace_graph {X : Type*} [TopologicalSpace X]
    {r h : X → ℝ} (hr : Continuous r) (hh : Continuous h) :
    IsClosed {w : X × ℂ | w.2 ∈ hankelTrace (r w.1) (h w.1)} := by
  simp_rw [mem_hankelTrace_iff]
  exact (((isClosed_le (Complex.continuous_re.comp continuous_snd) (hr.comp continuous_fst)).inter
    (isClosed_eq (Complex.continuous_im.comp continuous_snd) (hh.comp continuous_fst).neg)).union
      ((isClosed_eq (Complex.continuous_re.comp continuous_snd) (hr.comp continuous_fst)).inter
        ((isClosed_le (hh.comp continuous_fst).neg (Complex.continuous_im.comp continuous_snd)).inter
          (isClosed_le (Complex.continuous_im.comp continuous_snd) (hh.comp continuous_fst))))).union
    ((isClosed_le (Complex.continuous_re.comp continuous_snd) (hr.comp continuous_fst)).inter
      (isClosed_eq (Complex.continuous_im.comp continuous_snd) (hh.comp continuous_fst)))

theorem isClosed_hankelTrace (r h : ℝ) : IsClosed (hankelTrace r h) :=
  (isClosed_hankelTrace_graph (r := fun _ : ℂ => r) (h := fun _ : ℂ => h)
    continuous_const continuous_const).preimage (continuous_id.prodMk continuous_id)

theorem saddleContourHeight_saddle {c : ℝ} (hc : 0 < c) (j : Branch) :
    saddleContourHeight c j ((c : ℂ) * rho j) =
      match j with | .one | .two => complexHeight c | .three => c := by
  cases j
  · simp [saddleContourHeight, Complex.mul_im, rho_one_im, complexHeight,
      abs_mul, abs_of_pos hc]
    rw [abs_of_nonneg (by positivity)]
    ring
  · simp [saddleContourHeight, Complex.mul_im, rho_two_im, complexHeight,
      abs_mul, abs_of_pos hc]
    rw [abs_of_nonneg (by positivity)]
    ring
  · rfl

theorem saddleContour_limiting_gap {c : ℝ} (hc : 0 < c) (j : Branch) {s : ℂ}
    (hs : s ∈ hankelTrace (saddleContourRight c j ((c : ℂ) * rho j))
      (saddleContourHeight c j ((c : ℂ) * rho j)))
    (hne : s ≠ (c : ℂ) * rho j) :
    0 < (limitingPhase j c ((c : ℂ) * rho j)).re - (limitingPhase j c s).re := by
  cases j
  · have h := hankel_phase_gap_one hc (by
      simpa only [saddleContourRight, saddleContourHeight_saddle hc, complexRight] using hs) hne
    simpa only [limitingPhase_one_saddle_re hc, sub_pos] using h
  · have h := hankel_phase_gap_two hc (by
      simpa only [saddleContourRight, saddleContourHeight_saddle hc, complexRight] using hs) hne
    simpa only [limitingPhase_two_saddle_re hc, sub_pos] using h
  · have h := hankel_phase_gap_three hc (by
      simpa only [saddleContourRight, saddleContourHeight, rho_three, mul_one, Complex.ofReal_re] using hs) hne
    simpa only [limitingPhase_three_saddle_re hc, sub_pos] using h

@[expose] noncomputable def boundedContourAway (c : ℝ) (j : Branch) (δ M : ℝ) : Set ℂ :=
  {s | s ∈ hankelTrace (saddleContourRight c j ((c : ℂ) * rho j))
      (saddleContourHeight c j ((c : ℂ) * rho j)) ∧
    ‖s‖ ≤ M ∧ δ ≤ ‖s - (c : ℂ) * rho j‖}

theorem isCompact_boundedContourAway (c : ℝ) (j : Branch) (δ M : ℝ) :
    IsCompact (boundedContourAway c j δ M) := by
  exact (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset
    ((isClosed_hankelTrace _ _).inter ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)))
    (fun s hs => by simpa only [mem_closedBall, dist_zero_right] using hs.2.1)

theorem exists_uniform_limiting_gap {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (j : Branch) (M : ℝ) :
    ∃ ε > 0, ∀ s ∈ boundedContourAway c j δ M,
      ε ≤ (limitingPhase j c ((c : ℂ) * rho j)).re - (limitingPhase j c s).re := by
  have hslit : boundedContourAway c j δ M ⊆ Complex.slitPlane := by
    intro s hs
    have hζ : (c : ℂ) * rho j ∈ saddleDisk c j := mem_closedBall_self (by positivity)
    exact hankelTrace_mem_slitPlane (saddleContourRight_bounds hc j hζ).1
      (by have hh := (saddleContourHeight_bounds hc j hζ).1; linarith) hs.1
  refine (isCompact_boundedContourAway c j δ M).exists_forall_le'
    (continuousOn_const.sub (Complex.continuous_re.comp_continuousOn
      ((differentiableOn_limitingPhase j hc).continuousOn.mono hslit))) ?_
  exact fun s hs => saddleContour_limiting_gap hc j hs.1 (by
    intro he
    have h := hs.2.2
    rw [he, sub_self, norm_zero] at h
    linarith)

theorem persistent_gap_near_fiber {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    {f : ℂ × ℂ → ℝ} (hf : ContinuousOn f K) {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hbase : ∀ w ∈ K, w.1 = a → ε ≤ f w) :
    ∀ᶠ σ : ℂ in 𝓝 a, ∀ s : ℂ, (σ, s) ∈ K → ε / 2 ≤ f (σ, s) := by
  have hbad : IsCompact (K ∩ f ⁻¹' Iic (ε / 2)) :=
    hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic) inter_subset_left
  have hnot : a ∉ Prod.fst '' (K ∩ f ⁻¹' Iic (ε / 2)) := by
    rintro ⟨w, ⟨hw, hfw⟩, hwa⟩
    have h := hbase w hw hwa
    change f w ≤ ε / 2 at hfw
    linarith
  filter_upwards [((hbad.image continuous_fst).isClosed.isOpen_compl.mem_nhds hnot)] with σ hσ s hs
  exact le_of_not_gt (fun h => hσ ⟨(σ, s), ⟨hs, h.le⟩, rfl⟩)

@[expose] noncomputable def boundedMovingContour (c : ℝ) (j : Branch) (δ M : ℝ) : Set (ℂ × ℂ) :=
  {w | w.1 ∈ saddleDisk c j ∧
    w.2 ∈ hankelTrace (saddleContourRight c j w.1) (saddleContourHeight c j w.1) ∧
    ‖w.2‖ ≤ M ∧ δ ≤ ‖w.2 - w.1‖}

theorem isCompact_boundedMovingContour (c : ℝ) (j : Branch) (δ M : ℝ) :
    IsCompact (boundedMovingContour c j δ M) := by
  exact ((isCompact_closedBall ((c : ℂ) * rho j) (c / 4)).prod
    (isCompact_closedBall (0 : ℂ) M)).of_isClosed_subset
    (((isClosed_closedBall.preimage continuous_fst).inter
      ((isClosed_hankelTrace_graph (continuous_saddleContourRight c j) (continuous_saddleContourHeight c j)).inter
        ((isClosed_le continuous_snd.norm continuous_const).inter
          (isClosed_le continuous_const (continuous_snd.sub continuous_fst).norm)))))
    (fun w hw => ⟨hw.1, by simpa only [mem_closedBall, dist_zero_right] using hw.2.2.1⟩)

theorem continuousOn_limitingContourGap {c : ℝ} (hc : 0 < c) (j : Branch) (δ M : ℝ) :
    ContinuousOn (fun w : ℂ × ℂ => (limitingPhase j c w.1).re - (limitingPhase j c w.2).re)
      (boundedMovingContour c j δ M) := by
  have hslit : ∀ w ∈ boundedMovingContour c j δ M,
      w.1 ∈ Complex.slitPlane ∧ w.2 ∈ Complex.slitPlane := by
    intro w hw
    exact ⟨saddleDisk_mem_slitPlane hc j hw.1,
      hankelTrace_mem_slitPlane (saddleContourRight_bounds hc j hw.1).1
        (by have hh := (saddleContourHeight_bounds hc j hw.1).1; linarith) hw.2.1⟩
  exact (Complex.continuous_re.comp_continuousOn
    ((differentiableOn_limitingPhase j hc).continuousOn.comp continuous_fst.continuousOn
      (fun w hw => (hslit w hw).1))).sub
    (Complex.continuous_re.comp_continuousOn
      ((differentiableOn_limitingPhase j hc).continuousOn.comp continuous_snd.continuousOn
        (fun w hw => (hslit w hw).2)))

/-- The limiting phase gap persists uniformly on every bounded contour piece
away from the center, even as the chosen contour moves with that center. -/
theorem exists_uniform_perturbed_limiting_gap {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (j : Branch) (M : ℝ) :
    ∃ ε > 0, ∀ᶠ σ : ℂ in 𝓝 ((c : ℂ) * rho j), ∀ s : ℂ,
      s ∈ hankelTrace (saddleContourRight c j σ) (saddleContourHeight c j σ) →
      ‖s‖ ≤ M → δ ≤ ‖s - σ‖ →
      ε ≤ (limitingPhase j c σ).re - (limitingPhase j c s).re := by
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_limiting_gap hc hδ j M
  have hp := persistent_gap_near_fiber (isCompact_boundedMovingContour c j δ M)
    (continuousOn_limitingContourGap hc j δ M) (a := (c : ℂ) * rho j) hε (by
      intro w hw he
      rw [he]
      exact hgap w.2 ⟨by simpa only [he] using hw.2.1, hw.2.2.1,
        by simpa only [he] using hw.2.2.2⟩)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [hp, isOpen_ball.mem_nhds
    (mem_ball_self (show 0 < c / 4 by positivity))]
    with σ hσ hσD s hs hM hd
  exact hσ s ⟨ball_subset_closedBall hσD, hs, hM, hd⟩

theorem exists_uniform_limiting_gap_near_exact_saddles [PositiveArgument] {α₁ α₂ δ : ℝ}
    (h₁ : 0 < α₁) (h₂ : 0 < α₂) (hδ : 0 < δ) (j : Branch) (M D : ℝ) :
    ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ σ : ℂ,
      ‖σ - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ D * smallParameter n →
      ∀ s : ℂ, s ∈ hankelTrace (saddleContourRight (saddleScale α₁ α₂) j σ)
        (saddleContourHeight (saddleScale α₁ α₂) j σ) →
      ‖s‖ ≤ M → δ ≤ ‖s - σ‖ →
      ε ≤ (limitingPhase j (saddleScale α₁ α₂) σ).re -
        (limitingPhase j (saddleScale α₁ α₂) s).re := by
  obtain ⟨ε, hε, hn⟩ := exists_uniform_perturbed_limiting_gap (saddleScale_pos h₁ h₂) hδ j M
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hn
  have hsmall : ∀ᶠ n : ℕ in atTop, D * smallParameter n < r :=
    (show Tendsto (fun n => D * smallParameter n) atTop (𝓝 0) by
      simpa only [mul_zero] using smallParameter_tendsto.const_mul D).eventually (gt_mem_nhds hr)
  exact ⟨ε, hε, hsmall.mono fun n hn σ hσ =>
    hball σ (by simpa only [mem_ball, dist_eq_norm] using hσ.trans_lt hn)⟩

end ThisWork.Analytic
