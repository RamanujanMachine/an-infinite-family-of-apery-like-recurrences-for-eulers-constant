module
public import ThisWork.Trajectory.GrowingContourChoice
public import ThisWork.LowerWindowRemainder
/-! Finite growing-contour remainders outside the reflected saddle window. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

noncomputable def growingMomentKernel (m d : ℕ) (A₁ A₂ z : ℝ) (n k : ℕ) (s : ℂ) : ℂ :=
  s ^ k * kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * s)

theorem eventually_continuousOn_growing_moment_contour {A₁ A₂ z c η : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hc : 0 < c) (hη : 0 < η) (m d k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ContinuousOn (growingMomentKernel m d A₁ A₂ z n k) (hankelTrace c η) := by
  filter_upwards [eventually_right_factor_conditions h₁ c,
    eventually_right_factor_conditions h₂ c, eventually_gt_atTop (0 : ℕ)] with n hn₁ hn₂ hn
  have hupper : sqrtScale n * c < min (A₁ * n + 1) (A₂ * n + 1) :=
    lt_min (by linarith [hn₁.1, hn₁.2]) (by linarith [hn₂.1, hn₂.2])
  have hK := (differentiableOn_kernel hz m d A₁ A₂ .one n).continuousOn.comp
    (s := hankelTrace c η) (by fun_prop : Continuous (fun s : ℂ => (sqrtScale n : ℂ) * s)).continuousOn
    (fun s hs => scaled_hankelTrace_mem_kernelDomain n (sqrtScale_pos hn) hc hη hupper hs)
  exact (continuous_id.pow k).continuousOn.mul hK

private theorem norm_horizontal_point_le {c η T : ℝ} (hc : 0 < c) (hη : η ≤ c) (hT : 2 * c ≤ T)
    {s : ℂ} (hr : -T ≤ s.re ∧ s.re ≤ c) (hi : |s.im| ≤ η) : ‖s‖ ≤ T + 2 * c := by
  have habs : |s.re| ≤ T := abs_le.mpr ⟨hr.1, by linarith [hr.2]⟩
  exact (Complex.norm_le_abs_re_add_abs_im s).trans (by linarith)

namespace ReflectedSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
    (G : GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius)

theorem uniform_finite_growing_window_remainder {T : ℝ}
    (hT : 2 * doubleSaddleScale d A₁ A₂ z ≤ T) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖finiteHankelIntegral (-T) (doubleSaddleScale d A₁ A₂ z) G.height
          (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
        contourWindow .one (-F.center n) F.data.rightWidth F.data.leftWidth
          (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k)‖ ≤
        C * doubleScale m d A₁ A₂ z (F.index n) *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  let M := T + 2 * c
  have hc : 0 < c := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  have hM : c ≤ M := by dsimp only [M]; linarith
  have hM₀ : 0 ≤ M := hc.le.trans hM
  have hT₀ : 0 ≤ T := by linarith
  have hheight : 0 < G.height := G.height_pos
  refine ⟨(2 * (c + T) + 2 * G.height) * M ^ k, by positivity, ?_⟩
  filter_upwards [F.index_tendsto.eventually (G.uniform_lower_gap F.d_pos F.A₁_pos F.A₂_pos F.z_pos rfl hM m),
    F.index_tendsto.eventually (uniform_growing_upper_bound F.d_pos F.A₁_pos F.A₂_pos F.z_pos
      G.height_pos (G.height_le hc) (by linarith [G.height_pi]) hM m),
    F.index_tendsto.eventually (uniform_growing_right_bound F.d_pos F.A₁_pos F.A₂_pos F.z_pos
      G.height_pos (G.height_le hc) G.height_pi m),
    F.index_tendsto.eventually (eventually_continuousOn_growing_moment_contour F.A₁_pos F.A₂_pos F.z_pos
      hc G.height_pos m d k), F.eventually_center_displacement_lt F.windowRadius_pos,
    F.index_tendsto.eventually (eventually_gt_atTop (0 : ℕ))]
    with n hlower hupper hright hcont hdisp hn
  let R := sqrtScale (F.index n)
  let H := doubleScale m d A₁ A₂ z (F.index n)
  let E := M ^ k * H * Real.exp ((2 * c - G.rate) * R)
  have hH : 0 < H := doubleScale_pos F.d_pos hn F.A₁_pos F.A₂_pos F.z_pos
  have hR : 0 < R := sqrtScale_pos hn
  have hcenter := (Complex.abs_re_le_norm (F.center n - (c : ℂ))).trans_lt hdisp
  simp only [Complex.sub_re, Complex.ofReal_re] at hcenter
  have hcenterLo := (abs_lt.mp hcenter).1
  have hcenterHi := (abs_lt.mp hcenter).2
  have hδpos := F.windowRadius_pos
  have hwidth₁ : 4 * F.windowRadius ≤ F.data.leftWidth := by
    dsimp only [windowRadius]
    linarith [min_le_left F.data.leftWidth F.data.rightWidth]
  have hwidth₂ : 4 * F.windowRadius ≤ F.data.rightWidth := by
    dsimp only [windowRadius]
    linarith [min_le_right F.data.leftWidth F.data.rightWidth]
  have ha : F.data.leftWidth < c / 16 := F.data.widths_lt.1
  have hb : F.data.rightWidth < c / 16 := F.data.widths_lt.2
  have hδc : F.windowRadius < c / 16 := by linarith [F.windowRadius_pos]
  have hleft : -T ≤ (-F.center n).re - F.data.rightWidth := by
    rw [Complex.neg_re]
    linarith [(abs_lt.mp hcenter).2]
  have hright' : (-F.center n).re + F.data.leftWidth ≤ c := by
    rw [Complex.neg_re]
    linarith [(abs_lt.mp hcenter).1]
  have hweight (s : ℂ) (hs : ‖s‖ ≤ M) (hK : ‖kernel m d A₁ A₂ z .one (F.index n) ((R : ℂ) * s)‖ ≤
      H * Real.exp ((2 * c - G.rate) * R)) : ‖growingMomentKernel m d A₁ A₂ z (F.index n) k s‖ ≤ E := by
    rw [growingMomentKernel, norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hs k) hK (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have heUpper : G.rate ≤ 5 * Real.pi * G.height / 2 := by
    have h := (min_le_right (G.gap / 2) _).trans (min_le_left (Real.pi * G.height / 2) c)
    change G.rate ≤ Real.pi * G.height / 2 at h
    linarith [mul_pos Real.pi_pos G.height_pos]
  have heRight : G.rate ≤ c := (min_le_right (G.gap / 2) _).trans (min_le_right _ c)
  have hbnd := norm_finiteHankel_sub_lowerWindow_le G.height_pos.le F.data.widths_pos.2.le F.data.widths_pos.1.le
    (by positivity : 0 ≤ E) hleft hright' hcont
    (hlo := fun u hu => ?_) (hro := fun u hu => ?_) (hu := fun u hu => ?_) (hv := fun v hv => ?_)
  · exact hbnd.trans_eq (by dsimp only [E]; ring)
  · simp only [Complex.neg_re] at hu
    have hu' : -T ≤ u ∧ u ≤ c := ⟨hu.1, by linarith [hu.2, F.data.widths_pos.1, F.data.widths_pos.2]⟩
    let s : ℂ := -(u : ℂ) + (G.height : ℂ) * Complex.I
    have hsre : s.re = -u := by simp [s, Complex.mul_re]
    have hsim : s.im = G.height := by simp [s, Complex.mul_im]
    have hsM : ‖s‖ ≤ M := (Complex.norm_le_abs_re_add_abs_im s).trans (by
      rw [hsre, hsim, abs_neg, abs_of_pos G.height_pos]
      have huabs : |u| ≤ T := abs_le.mpr ⟨hu'.1, by linarith [hu'.2]⟩
      dsimp only [M]
      linarith [G.height_le hc])
    have hg := hlower s hsM (by rw [hsre]; linarith [hu'.2]) hsim (by
      have hbnd : F.windowRadius ≤ s.re - c := by
        rw [hsre]
        linarith [(abs_lt.mp hcenter).1, hu.2]
      exact hbnd.trans (le_abs_self _))
    have hsneg : -s = (u : ℂ) - (G.height : ℂ) * Complex.I := by dsimp only [s]; ring
    rw [← hsneg]
    exact hweight (-s) (by simpa only [norm_neg] using hsM) hg
  · simp only [Complex.neg_re] at hu
    have hu' : -T ≤ u ∧ u ≤ c := ⟨by linarith [hu.1], hu.2⟩
    let s : ℂ := -(u : ℂ) + (G.height : ℂ) * Complex.I
    have hsre : s.re = -u := by simp [s, Complex.mul_re]
    have hsim : s.im = G.height := by simp [s, Complex.mul_im]
    have hsM : ‖s‖ ≤ M := (Complex.norm_le_abs_re_add_abs_im s).trans (by
      rw [hsre, hsim, abs_neg, abs_of_pos G.height_pos]
      have huabs : |u| ≤ T := abs_le.mpr ⟨hu'.1, by linarith [hu'.2]⟩
      dsimp only [M]
      linarith [G.height_le hc])
    have hg := hlower s hsM (by rw [hsre]; linarith [hu'.2]) hsim (by
      have hbnd : F.windowRadius ≤ c - s.re := by rw [hsre]; linarith [hu.1]
      rw [abs_sub_comm]
      exact hbnd.trans (le_abs_self _))
    have hsneg : -s = (u : ℂ) - (G.height : ℂ) * Complex.I := by dsimp only [s]; ring
    rw [← hsneg]
    exact hweight (-s) (by simpa only [norm_neg] using hsM) hg
  · let s : ℂ := -(u : ℂ) + (G.height : ℂ) * Complex.I
    have hsre : s.re = -u := by simp [s, Complex.mul_re]
    have hsim : s.im = G.height := by simp [s, Complex.mul_im]
    have hsM : ‖s‖ ≤ M := (Complex.norm_le_abs_re_add_abs_im s).trans (by
      rw [hsre, hsim, abs_neg, abs_of_pos G.height_pos]
      have hu' : -T ≤ u ∧ u ≤ c := hu
      have huabs : |u| ≤ T := abs_le.mpr ⟨hu'.1, by linarith [hu'.2]⟩
      dsimp only [M]
      linarith [G.height_le hc])
    have hsconj : -(starRingEnd ℂ) s = (u : ℂ) + (G.height : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [s, Complex.mul_re, Complex.mul_im]
    rw [← hsconj]
    apply hweight _ (by simpa only [norm_neg, Complex.norm_conj] using hsM)
    exact (hupper s hsM (by rw [hsre]; have hu' : u ≤ c := hu.2; linarith) hsim).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right heUpper hR.le])) hH.le)
  · have hv' : -G.height ≤ v ∧ v ≤ G.height := hv
    have hsre : ((c : ℂ) + (v : ℂ) * Complex.I).re = c := by simp [Complex.mul_re]
    have hsim : ((c : ℂ) + (v : ℂ) * Complex.I).im = v := by simp [Complex.mul_im]
    apply hweight _ (norm_horizontal_point_le hc (G.height_le hc) hT
      (by rw [hsre]; constructor <;> linarith) (by rw [hsim]; exact abs_le.mpr hv'))
    exact (hright _ hsre (by rw [hsim]; exact abs_le.mpr hv')).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right heRight hR.le])) hH.le)

end ReflectedSaddleData
end ThisWork.Trajectory
