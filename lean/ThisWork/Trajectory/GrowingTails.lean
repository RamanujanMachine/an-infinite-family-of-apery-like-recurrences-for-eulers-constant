module
public import ThisWork.Trajectory.GrowingFiniteRemainder
public import ThisWork.Trajectory.TailIntegrals
public import ThisWork.FullWindowRemainder
/-! The infinite tails of the fixed-height growing contour. -/
@[expose] public section
namespace ThisWork.Trajectory.ReflectedSaddleData
open Set Filter Metric MeasureTheory Analytic
open scoped Topology
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
    (G : GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius)

theorem uniform_growing_hankel_truncation (k : ℕ) :
    ∃ T ≥ 1, 2 * doubleSaddleScale d A₁ A₂ z ≤ T ∧ ∃ C ≥ 0,
      ∀ᶠ n : ℕ in atTop,
      ‖hankelIntegral (doubleSaddleScale d A₁ A₂ z) G.height
          (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
        finiteHankelIntegral (-T) (doubleSaddleScale d A₁ A₂ z) G.height
          (growingMomentKernel m d A₁ A₂ z (F.index n) k)‖ ≤
        C * doubleScale m d A₁ A₂ z (F.index n) *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  obtain ⟨T₀, hT₀, hb⟩ := uniform_integrated_leftMoment_tail F.d_pos F.A₁_pos F.A₂_pos F.z_pos
    G.height_pos G.height_pos.le zero_lt_one m .one k
  let T := max T₀ (2 * c)
  have hT : 2 * c ≤ T := le_max_right _ _
  have hT₁ : 1 ≤ T := hT₀.trans (le_max_left _ _)
  have hM : c ≤ T + 2 * c := by linarith
  refine ⟨T, hT₁, hT, 2 * Real.exp T, by positivity, ?_⟩
  filter_upwards [F.index_tendsto.eventually hb,
    F.index_tendsto.eventually (G.uniform_lower_gap F.d_pos F.A₁_pos F.A₂_pos F.z_pos rfl hM m),
    F.index_tendsto.eventually (uniform_growing_upper_bound F.d_pos F.A₁_pos F.A₂_pos F.z_pos
      G.height_pos (G.height_le hc) (by linarith [G.height_pi]) hM m),
    F.index_tendsto.eventually (eventually_continuousOn_growing_moment_contour F.A₁_pos F.A₂_pos F.z_pos hc G.height_pos m d k),
    (sqrtScale_tendsto.comp F.index_tendsto).eventually (eventually_ge_atTop (1 : ℝ))]
    with n htail hlower hupper hcont hR
  change 1 ≤ sqrtScale (F.index n) at hR
  let H := doubleScale m d A₁ A₂ z (F.index n)
  let E := H * Real.exp ((2 * c - G.rate) * sqrtScale (F.index n))
  have hn₀ : 0 < F.index n := by
    by_contra h
    have hzero : F.index n = 0 := by omega
    simp [hzero, sqrtScale] at hR
    linarith
  have hH : 0 < H := doubleScale_pos F.d_pos hn₀ F.A₁_pos F.A₂_pos F.z_pos
  let s : ℂ := (T : ℂ) + (G.height : ℂ) * Complex.I
  have hsM : ‖s‖ ≤ T + 2 * c := (Complex.norm_le_abs_re_add_abs_im s).trans (by
    simp only [s, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add, abs_of_nonneg (by linarith : 0 ≤ T), abs_of_pos G.height_pos]
    linarith [G.height_le hc])
  have hsre : s.re = T := by simp [s, Complex.mul_re]
  have hsim : s.im = G.height := by simp [s, Complex.mul_im]
  have hδ : F.windowRadius < c := by
    have hl : F.data.leftWidth < c / 16 := F.data.widths_lt.1
    have hbδ : 4 * F.windowRadius ≤ F.data.leftWidth := by
      dsimp only [windowRadius]
      linarith [min_le_left F.data.leftWidth F.data.rightWidth]
    linarith
  have hKL : ‖kernel m d A₁ A₂ z .one (F.index n)
      ((sqrtScale (F.index n) : ℂ) * (-(T : ℂ) + (-G.height : ℝ) * Complex.I))‖ ≤ E := by
    have h := hlower s hsM (by rw [hsre]; linarith) hsim (by
      rw [hsre]
      exact (show F.windowRadius ≤ T - c by linarith).trans (le_abs_self _))
    simpa only [s, neg_add_rev, Complex.ofReal_neg, neg_mul, neg_neg, add_comm] using h
  have hKU : ‖kernel m d A₁ A₂ z .one (F.index n)
      ((sqrtScale (F.index n) : ℂ) * (-(T : ℂ) + (G.height : ℂ) * Complex.I))‖ ≤ E := by
    have h := hupper s hsM (by rw [hsre]; linarith) hsim
    have hrate : G.rate ≤ 5 * Real.pi * G.height / 2 := by
      have h' : G.rate ≤ Real.pi * G.height / 2 :=
        (min_le_right (G.gap / 2) _).trans (min_le_left _ c)
      linarith [mul_pos Real.pi_pos G.height_pos]
    have h' : ‖kernel m d A₁ A₂ z .one (F.index n) ((sqrtScale (F.index n) : ℂ) * (-(starRingEnd ℂ) s))‖ ≤ E :=
      h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hrate (sqrtScale_pos hn₀).le])) hH.le)
    simpa [s, add_comm] using h'
  have htL := htail T (le_max_left _ _) (-G.height) (by rw [abs_neg, abs_of_pos G.height_pos])
    (by rw [abs_neg, abs_of_pos G.height_pos])
  have htU := htail T (le_max_left _ _) G.height (by rw [abs_of_pos G.height_pos])
    (by rw [abs_of_pos G.height_pos])
  have hL : ‖∫ t in Ioi T, leftMomentKernel m d A₁ A₂ z .one (F.index n) k (-G.height) t‖ ≤ Real.exp T * E :=
    htL.2.trans ((div_le_self (by positivity) (by simpa only [one_mul] using hR)).trans
      (mul_le_mul_of_nonneg_left hKL (Real.exp_pos _).le))
  have hU : ‖∫ t in Ioi T, leftMomentKernel m d A₁ A₂ z .one (F.index n) k G.height t‖ ≤ Real.exp T * E :=
    htU.2.trans ((div_le_self (by positivity) (by simpa only [one_mul] using hR)).trans
      (mul_le_mul_of_nonneg_left hKU (Real.exp_pos _).le))
  let f := growingMomentKernel m d A₁ A₂ z (F.index n) k
  have hel : (fun u : ℝ => f (((-u : ℝ) : ℂ) - (G.height : ℂ) * Complex.I)) =
      leftMomentKernel m d A₁ A₂ z .one (F.index n) k (-G.height) := by
    funext u
    simp only [f, growingMomentKernel, leftMomentKernel, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg]
  have heu : (fun u : ℝ => f (((-u : ℝ) : ℂ) + (G.height : ℂ) * Complex.I)) =
      leftMomentKernel m d A₁ A₂ z .one (F.index n) k G.height := by
    funext u
    simp only [f, growingMomentKernel, leftMomentKernel, Complex.ofReal_neg]
  have il := integrableOn_Iic_of_reflected_tail (continuousOn_lower_of_continuousTrace hcont)
    (show IntegrableOn (fun u : ℝ => f (((-u : ℝ) : ℂ) - (G.height : ℂ) * Complex.I)) (Ioi T) by rw [hel]; exact htL.1)
  have iu := integrableOn_Iic_of_reflected_tail (continuousOn_upper_of_continuousTrace hcont)
    (show IntegrableOn (fun u : ℝ => f (((-u : ℝ) : ℂ) + (G.height : ℂ) * Complex.I)) (Ioi T) by rw [heu]; exact htU.1)
  rw [← hel, integral_comp_neg_Ioi T (fun u : ℝ => f ((u : ℂ) - (G.height : ℂ) * Complex.I))] at hL
  rw [← heu, integral_comp_neg_Ioi T (fun u : ℝ => f ((u : ℂ) + (G.height : ℂ) * Complex.I))] at hU
  have htrunc := norm_hankelIntegral_sub_truncation (left := -T) (by linarith : -T ≤ c) il iu
  exact htrunc.trans (by dsimp only [E] at hL hU; nlinarith)

/-- The complete original growing contour is localized to its lower window. -/
theorem uniform_full_growing_lower_window_remainder (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖hankelIntegral (doubleSaddleScale d A₁ A₂ z) G.height
          (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
        contourWindow .one (-F.center n) F.data.rightWidth F.data.leftWidth
          (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k)‖ ≤
        C * doubleScale m d A₁ A₂ z (F.index n) *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
  obtain ⟨T, _, hT, Ct, hCt, ht⟩ := F.uniform_growing_hankel_truncation G k
  obtain ⟨Cf, hCf, hf⟩ := F.uniform_finite_growing_window_remainder G hT k
  refine ⟨Ct + Cf, add_nonneg hCt hCf, ?_⟩
  filter_upwards [ht, hf] with n htn hfn
  have htri := norm_add_le
    (hankelIntegral (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
      finiteHankelIntegral (-T) (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k))
    (finiteHankelIntegral (-T) (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
      contourWindow .one (-F.center n) F.data.rightWidth F.data.leftWidth
        (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k))
  rw [sub_add_sub_cancel] at htri
  exact htri.trans ((add_le_add htn hfn).trans_eq (by ring))

end ThisWork.Trajectory.ReflectedSaddleData
