module
public import ThisWork.Trajectory.GrowingContourChoice
public import ThisWork.Trajectory.SqrtLogError
public import ThisWork.HorizontalRectangleBound
public import ThisWork.WindowOrientation
/-! Deforming the reflected lower window through its moving Gaussian saddle. -/
@[expose] public section
namespace ThisWork.Trajectory.ReflectedSaddleData
open Set Filter Metric MeasureTheory Analytic
open scoped Topology
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
    (G : GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius)

noncomputable def heightMoment (n k : ℕ) (y : ℝ) : ℂ :=
  ∫ u in (F.center n).re - F.data.leftWidth..(F.center n).re + F.data.rightWidth,
    ((u : ℂ) + (y : ℂ) * Complex.I) ^ k *
      reflectedScaledKernel m d A₁ A₂ z (F.index n) ((u : ℂ) + (y : ℂ) * Complex.I)

theorem heightMoment_center (n k : ℕ) : F.heightMoment n k (F.center n).im = F.windowMoment n k := by
  exact horizontal_window_shift (fun s => s ^ k * reflectedScaledKernel m d A₁ A₂ z (F.index n) s)
    (F.center n) F.data.leftWidth F.data.rightWidth (F.center n).im rfl

theorem heightWindow_mem_ball (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc ((F.center n).re - F.data.leftWidth) ((F.center n).re + F.data.rightWidth)) :
    (u : ℂ) + (G.height : ℂ) * Complex.I ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ)
      (doubleSaddleScale d A₁ A₂ z / 4) ∧ 0 < u := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  have hσ : ‖F.center n - (c : ℂ)‖ < c / 16 := by
    simpa only [mem_ball, dist_eq_norm, center, c] using F.family.saddle_mem (n + F.data.shift)
  have hσr := (Complex.abs_re_le_norm (F.center n - (c : ℂ))).trans_lt hσ
  simp only [Complex.sub_re, Complex.ofReal_re] at hσr
  have ha : F.data.leftWidth < c / 16 := F.data.widths_lt.1
  have hb : F.data.rightWidth < c / 16 := F.data.widths_lt.2
  have hu' : (F.center n).re - F.data.leftWidth ≤ u ∧ u ≤ (F.center n).re + F.data.rightWidth := hu
  have hur : |u - c| < c / 8 := abs_lt.mpr ⟨by linarith [(abs_lt.mp hσr).1], by linarith [(abs_lt.mp hσr).2]⟩
  refine ⟨?_, by linarith [(abs_lt.mp hur).1]⟩
  rw [mem_ball, dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + (G.height : ℂ) * Complex.I - (c : ℂ))
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero, zero_add, abs_of_pos G.height_pos] at hn
  linarith [G.height_small]

theorem uniform_reflected_window_deformation (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖F.heightMoment n k G.height - F.windowMoment n k‖ ≤
        C * doubleScale m d A₁ A₂ z (F.index n) *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  obtain ⟨C, _, hk⟩ := uniform_log_norm_reflected_kernel_disk F.d_pos F.A₁_pos F.A₂_pos F.z_pos m
  refine ⟨4 * G.height * (2 * c) ^ k, by positivity [G.height_pos], ?_⟩
  filter_upwards [F.index_tendsto.eventually hk,
    F.index_tendsto.eventually (eventually_const_log_sqrt_le C (half_pos G.gap_pos)),
    F.index_tendsto.eventually (eventually_reflectedScaledKernel_regular F.d_pos F.A₁_pos F.A₂_pos hc m),
    F.eventually_center_displacement_lt (lt_min F.windowRadius_pos (half_pos G.height_pos))]
    with n hkernel hsmall hreg hdisp
  let σ := F.center n
  let f : ℂ → ℂ := fun s => s ^ k * reflectedScaledKernel m d A₁ A₂ z (F.index n) s
  let H := doubleScale m d A₁ A₂ z (F.index n)
  let R := sqrtScale (F.index n)
  let E := (2 * c) ^ k * H * Real.exp ((2 * c - G.rate) * R)
  have hH : 0 < H := doubleScale_pos F.d_pos hreg.1 F.A₁_pos F.A₂_pos F.z_pos
  have hR : 0 < R := sqrtScale_pos hreg.1
  have hsr : |σ.re - c| < F.windowRadius := by
    have h := (Complex.abs_re_le_norm (σ - (c : ℂ))).trans_lt (hdisp.trans_le (min_le_left _ _))
    simpa only [Complex.sub_re, Complex.ofReal_re] using h
  have hsi : |σ.im| < G.height / 2 := by
    have h := (Complex.abs_im_le_norm (σ - (c : ℂ))).trans_lt (hdisp.trans_le (min_le_right _ _))
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  have ha : F.data.leftWidth < c / 16 := F.data.widths_lt.1
  have hb : F.data.rightWidth < c / 16 := F.data.widths_lt.2
  have hδ : F.windowRadius < c / 16 := by
    have hmin := min_le_left F.data.leftWidth F.data.rightWidth
    dsimp only [windowRadius]
    linarith [F.data.widths_pos.1, F.data.widths_pos.2]
  have hheight : 0 < G.height := G.height_pos
  have hheightc : G.height ≤ c / 32 := G.height_small
  have hvabs (v : ℝ) (hv : v ∈ uIcc G.height σ.im) : |v| ≤ G.height := by
    have hs : σ.im ≤ G.height := by linarith [(abs_lt.mp hsi).2]
    rw [uIcc_of_ge hs] at hv
    have hv' : σ.im ≤ v ∧ v ≤ G.height := hv
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hsi).1], hv'.2⟩
  have hrect : ∀ s : ℂ, s.re ∈ uIcc (σ.re - F.data.leftWidth) (σ.re + F.data.rightWidth) →
      s.im ∈ uIcc G.height σ.im → s ∈ ball (c : ℂ) (c / 4) := by
    intro s hr hi
    rw [uIcc_of_le (by linarith [F.data.widths_pos.1, F.data.widths_pos.2] :
      σ.re - F.data.leftWidth ≤ σ.re + F.data.rightWidth)] at hr
    have hr' : σ.re - F.data.leftWidth ≤ s.re ∧ s.re ≤ σ.re + F.data.rightWidth := hr
    have hreal : |s.re - c| < c / 8 := abs_lt.mpr ⟨by linarith [(abs_lt.mp hsr).1], by linarith [(abs_lt.mp hsr).2]⟩
    have him := hvabs s.im hi
    rw [mem_ball, dist_eq_norm]
    have hbnd := Complex.norm_le_abs_re_add_abs_im (s - (c : ℂ))
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hbnd
    linarith
  have hf : DifferentiableOn ℂ f (ball (c : ℂ) (c / 4)) :=
    (differentiableOn_id.pow k).mul (fun s hs => (hreg.2 s hs).1.differentiableWithinAt)
  have hside (t : ℝ) (ht : t = σ.re - F.data.leftWidth ∨ t = σ.re + F.data.rightWidth)
      (v : ℝ) (hv : v ∈ uIcc G.height σ.im) : ‖f ((t : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E := by
    let s : ℂ := (t : ℂ) + (v : ℂ) * Complex.I
    have hsre : s.re = t := by simp [s, Complex.mul_re]
    have hsim : s.im = v := by simp [s, Complex.mul_im]
    have htmem : t ∈ uIcc (σ.re - F.data.leftWidth) (σ.re + F.data.rightWidth) := by
      rcases ht with rfl | rfl
      · exact left_mem_uIcc
      · exact right_mem_uIcc
    have hsdisk : s ∈ saddleDisk c .three := by
      simpa only [saddleDisk, rho_three, mul_one] using ball_subset_closedBall (hrect s (by rw [hsre]; exact htmem) (by rw [hsim]; exact hv))
    have hnorm : ‖s‖ ≤ 2 * c := (saddleDisk_norm_le hc .three hsdisk).trans (by linarith)
    have hre : -c ≤ s.re := by
      have h := saddleDisk_region hc .three hsdisk
      change c / 2 ≤ s.re at h
      linarith
    have hdist : F.windowRadius ≤ |s.re - c| := by
      have hL : 4 * F.windowRadius ≤ F.data.leftWidth := by
        dsimp only [windowRadius]
        linarith [min_le_left F.data.leftWidth F.data.rightWidth]
      have hB : 4 * F.windowRadius ≤ F.data.rightWidth := by
        dsimp only [windowRadius]
        linarith [min_le_right F.data.leftWidth F.data.rightWidth]
      have hδpos := F.windowRadius_pos
      rw [hsre]
      rcases ht with rfl | rfl
      · rw [abs_sub_comm]
        exact (show F.windowRadius ≤ c - (σ.re - F.data.leftWidth) by linarith [(abs_lt.mp hsr).2]).trans (le_abs_self _)
      · exact (show F.windowRadius ≤ σ.re + F.data.rightWidth - c by linarith [(abs_lt.mp hsr).1]).trans (le_abs_self _)
    have hp := G.phase_gap s hre (by rw [hsim]; exact hvabs v hv) hdist
    have hn := hkernel s hsdisk
    have hnormK : ‖reflectedScaledKernel m d A₁ A₂ z (F.index n) s‖ ≤
        H * Real.exp ((2 * c - G.rate) * R) := by
      apply norm_le_scale_exp_of_log_le hH
      have he : G.rate ≤ G.gap / 2 := min_le_left _ _
      nlinarith [(abs_le.mp hn).2, mul_le_mul_of_nonneg_right hp hR.le,
        mul_le_mul_of_nonneg_right he hR.le]
    rw [norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm k) hnormK (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hbound := norm_horizontal_rectangle_sub_le hf hrect
    (fun v hv => hside _ (Or.inl rfl) v hv) (fun v hv => hside _ (Or.inr rfl) v hv)
  rw [← F.heightMoment_center n k]
  exact hbound.trans (by
    have hv : |σ.im - G.height| ≤ 2 * G.height := abs_le.mpr ⟨by linarith [(abs_lt.mp hsi).1], by linarith [(abs_lt.mp hsi).2]⟩
    have hE : 0 ≤ E := by positivity
    have h := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * E by positivity)
    dsimp only [E] at h
    nlinarith)

end ThisWork.Trajectory.ReflectedSaddleData
