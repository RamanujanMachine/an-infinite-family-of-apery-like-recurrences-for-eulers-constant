module

public import ThisWork.Phase
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact

/-! The real logarithmic phase on the parabola `(a + i*b)^2`.
The saddle corresponds to `b = b₀`; `a > 0` keeps the curve off the cut. -/

@[expose] public section
namespace ThisWork

open Set

noncomputable def parabolicPoint (a b : ℝ) : ℂ := ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2

theorem parabolicPoint_mem_slitPlane {a : ℝ} (ha : 0 < a) (b : ℝ) :
    parabolicPoint a b ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hb : b = 0
  · left
    simp only [parabolicPoint, hb, Complex.ofReal_zero, zero_mul, add_zero,
      pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    positivity
  · right
    have hm : 2 * a * b ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') hb
    convert hm using 1
    simp only [parabolicPoint, pow_two, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub, add_zero, zero_add, neg_zero]
    ring

theorem arg_right_halfplane {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I) = Real.arctan (b / a) := by
  have hh := Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (show 0 < ((a : ℂ) + (b : ℂ) * Complex.I).re by simpa using ha))
  have he := Real.arctan_tan (abs_lt.mp hh).1 (abs_lt.mp hh).2
  rw [Complex.tan_arg] at he
  simpa using he.symm

theorem log_parabolicPoint {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Complex.log (parabolicPoint a b) =
      2 * Complex.log ((a : ℂ) + (b : ℂ) * Complex.I) := by
  have hn : (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith
  have hh := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (show 0 < ((a : ℂ) + (b : ℂ) * Complex.I).re by simpa using ha)))
  rw [parabolicPoint, pow_two, Complex.log_mul hn hn ⟨by linarith [hh.1], by linarith [hh.2]⟩]
  ring

noncomputable def parabolicPhase (a b₀ b : ℝ) : ℝ :=
  (a ^ 2 - b ^ 2) * (Real.log (a ^ 2 + b ^ 2) - Real.log (a ^ 2 + b₀ ^ 2) - 1) -
    4 * a * b * (Real.arctan (b / a) - Real.arctan (b₀ / a))

theorem phase_re_parabolicPoint (r : ℕ) {a : ℝ} (ha : 0 < a) (b₀ b : ℝ) :
    (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2) (parabolicPoint a b)).re =
      (r : ℝ) * parabolicPhase a b₀ b := by
  have hc : 0 < a ^ 2 + b₀ ^ 2 := by positivity
  have hs : parabolicPoint a b ≠ 0 := Complex.slitPlane_ne_zero (parabolicPoint_mem_slitPlane ha b)
  have hdiv : Complex.log (parabolicPoint a b / ((a ^ 2 + b₀ ^ 2 : ℝ) : ℂ)) =
      Complex.log (parabolicPoint a b) - (Real.log (a ^ 2 + b₀ ^ 2) : ℂ) := by
    rw [show parabolicPoint a b / ((a ^ 2 + b₀ ^ 2 : ℝ) : ℂ) =
        (((a ^ 2 + b₀ ^ 2)⁻¹ : ℝ) : ℂ) * parabolicPoint a b by push_cast; ring,
      Complex.log_ofReal_mul (inv_pos.mpr hc) hs, Real.log_inv, Complex.ofReal_neg]
    ring
  have hn : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hl : 2 * Real.log ‖(a : ℂ) + (b : ℂ) * Complex.I‖ = Real.log (a ^ 2 + b ^ 2) := by
    calc
      _ = Real.log (‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2) := (Real.log_pow _ 2).symm
      _ = _ := by rw [hn]
  have hre : (parabolicPoint a b).re = a ^ 2 - b ^ 2 := by
    simp [parabolicPoint, pow_two, Complex.mul_re]
  have him : (parabolicPoint a b).im = 2 * a * b := by
    simp [parabolicPoint, pow_two, Complex.mul_im]
    ring
  rw [Phase.phase, Phase.equation, hdiv, log_parabolicPoint ha b]
  simp [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im,
    arg_right_halfplane ha, hre, him, parabolicPhase]
  linear_combination ((r : ℝ) * (a ^ 2 - b ^ 2)) * hl

theorem hasDerivAt_parabolicPhase {a : ℝ} (ha : 0 < a) (b₀ b : ℝ) :
    HasDerivAt (parabolicPhase a b₀)
      (-2 * b * (Real.log (a ^ 2 + b ^ 2) - Real.log (a ^ 2 + b₀ ^ 2)) -
        4 * a * (Real.arctan (b / a) - Real.arctan (b₀ / a))) b := by
  have hD : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (a ^ 2 + t ^ 2))
      (2 * b / (a ^ 2 + b ^ 2)) b := by
    convert ((hasDerivAt_const b (a ^ 2)).add ((hasDerivAt_id b).pow 2)).log hD using 1
    · funext t
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      norm_num
  have har : HasDerivAt (fun t : ℝ => Real.arctan (t / a)) (a / (a ^ 2 + b ^ 2)) b := by
    convert ((hasDerivAt_id b).div_const a).arctan using 1
    · funext t
      simp only [id_eq]
    · simp only [id_eq]
      field_simp
  convert (((hasDerivAt_const b (a ^ 2)).sub ((hasDerivAt_id b).pow 2)).mul
    ((hlog.sub_const (Real.log (a ^ 2 + b₀ ^ 2))).sub_const 1)).sub
    (((hasDerivAt_id b).const_mul (4 * a)).mul (har.sub_const (Real.arctan (b₀ / a)))) using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    field_simp
    ring

theorem deriv_parabolicPhase_neg {a b₀ b : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b₀) (hb : b₀ < b) :
    deriv (parabolicPhase a b₀) b < 0 := by
  have hbpos : 0 < b := hb₀.trans_lt hb
  have hsq : a ^ 2 + b₀ ^ 2 < a ^ 2 + b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hb) (show 0 < b + b₀ by linarith)]
  have hlog : 0 < Real.log (a ^ 2 + b ^ 2) - Real.log (a ^ 2 + b₀ ^ 2) :=
    sub_pos.mpr (Real.log_lt_log (by positivity) hsq)
  have har : 0 < Real.arctan (b / a) - Real.arctan (b₀ / a) :=
    sub_pos.mpr (Real.arctan_lt_arctan_iff.mpr ((div_lt_div_iff_of_pos_right ha).mpr hb))
  rw [(hasDerivAt_parabolicPhase ha b₀ b).deriv]
  have h1 : 0 < 2 * b * (Real.log (a ^ 2 + b ^ 2) - Real.log (a ^ 2 + b₀ ^ 2)) := by positivity
  have h2 : 0 < 4 * a * (Real.arctan (b / a) - Real.arctan (b₀ / a)) := by positivity
  nlinarith

theorem deriv_parabolicPhase_pos {a b₀ b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hb₀ : b < b₀) :
    0 < deriv (parabolicPhase a b₀) b := by
  have hsq : a ^ 2 + b ^ 2 < a ^ 2 + b₀ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hb₀) (show 0 < b₀ + b by linarith)]
  have hlog : 0 < Real.log (a ^ 2 + b₀ ^ 2) - Real.log (a ^ 2 + b ^ 2) :=
    sub_pos.mpr (Real.log_lt_log (by positivity) hsq)
  have har : 0 < Real.arctan (b₀ / a) - Real.arctan (b / a) :=
    sub_pos.mpr (Real.arctan_lt_arctan_iff.mpr ((div_lt_div_iff_of_pos_right ha).mpr hb₀))
  rw [(hasDerivAt_parabolicPhase ha b₀ b).deriv]
  have h1 : 0 ≤ 2 * b * (Real.log (a ^ 2 + b₀ ^ 2) - Real.log (a ^ 2 + b ^ 2)) := by positivity
  have h2 : 0 < 4 * a * (Real.arctan (b₀ / a) - Real.arctan (b / a)) := by positivity
  nlinarith

theorem parabolicPhase_strict_max_nonneg {a b₀ b : ℝ} (ha : 0 < a)
    (hb₀ : 0 ≤ b₀) (hb : 0 ≤ b) (hne : b ≠ b₀) :
    parabolicPhase a b₀ b < parabolicPhase a b₀ b₀ := by
  by_cases hlt : b < b₀
  · have hm : StrictMonoOn (parabolicPhase a b₀) (Icc 0 b₀) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (fun x _ => (hasDerivAt_parabolicPhase ha b₀ x).continuousAt.continuousWithinAt)
        (fun x hx => by
          rw [interior_Icc] at hx
          exact deriv_parabolicPhase_pos ha hx.1.le hx.2)
    exact hm ⟨hb, hlt.le⟩ ⟨hb₀, le_rfl⟩ hlt
  · have hgt : b₀ < b := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    have hm : StrictAntiOn (parabolicPhase a b₀) (Ici b₀) :=
      strictAntiOn_of_deriv_neg (convex_Ici _)
        (fun x _ => (hasDerivAt_parabolicPhase ha b₀ x).continuousAt.continuousWithinAt)
        (fun x hx => by
          rw [interior_Ici] at hx
          exact deriv_parabolicPhase_neg ha hb₀ hx)
    exact hm le_rfl hgt.le hgt

theorem parabolicPhase_neg (a b₀ b : ℝ) :
    parabolicPhase a b₀ (-b) = parabolicPhase a b₀ b - 8 * a * b * Real.arctan (b₀ / a) := by
  simp only [parabolicPhase, neg_sq, neg_div, Real.arctan_neg]
  ring

theorem parabolicPhase_neg_neg (a b₀ b : ℝ) :
    parabolicPhase a (-b₀) (-b) = parabolicPhase a b₀ b := by
  simp only [parabolicPhase, neg_sq, neg_div, Real.arctan_neg]
  ring

theorem parabolicPhase_strict_max_of_nonneg_center {a b₀ b : ℝ}
    (ha : 0 < a) (hb₀ : 0 ≤ b₀) (hne : b ≠ b₀) :
    parabolicPhase a b₀ b < parabolicPhase a b₀ b₀ := by
  by_cases hb : 0 ≤ b
  · exact parabolicPhase_strict_max_nonneg ha hb₀ hb hne
  have hbneg : b < 0 := lt_of_not_ge hb
  have hbpos : 0 < -b := neg_pos.mpr hbneg
  have har : 0 ≤ Real.arctan (b₀ / a) := Real.arctan_nonneg.mpr (div_nonneg hb₀ ha.le)
  have he : parabolicPhase a b₀ b = parabolicPhase a b₀ (-b) -
      8 * a * (-b) * Real.arctan (b₀ / a) := by
    simpa only [neg_neg] using parabolicPhase_neg a b₀ (-b)
  by_cases hflip : -b = b₀
  · have hb₀pos : 0 < b₀ := by linarith
    have harpos : 0 < Real.arctan (b₀ / a) := Real.arctan_pos.mpr (div_pos hb₀pos ha)
    have hc : 0 < 8 * a * (-b) * Real.arctan (b₀ / a) := by positivity
    rw [he, hflip]
    exact sub_lt_self _ (by simpa only [hflip] using hc)
  · have hc : 0 ≤ 8 * a * (-b) * Real.arctan (b₀ / a) := by positivity
    calc
      _ ≤ parabolicPhase a b₀ (-b) := by rw [he]; exact sub_le_self _ hc
      _ < _ := parabolicPhase_strict_max_nonneg ha hb₀ (by linarith) hflip

/-- The logarithmic phase has a unique global maximum on every admissible
parabola, independently of rank and saddle angle. -/
theorem parabolicPhase_strict_max {a b₀ b : ℝ} (ha : 0 < a) (hne : b ≠ b₀) :
    parabolicPhase a b₀ b < parabolicPhase a b₀ b₀ := by
  by_cases hb₀ : 0 ≤ b₀
  · exact parabolicPhase_strict_max_of_nonneg_center ha hb₀ hne
  · have he : -b ≠ -b₀ := by
      intro h
      exact hne (neg_injective h)
    simpa only [parabolicPhase_neg_neg] using
      parabolicPhase_strict_max_of_nonneg_center ha (show 0 ≤ -b₀ by linarith) he

/-- The actual complex limiting phase has a unique dominant point on the
parabolic contour, for every positive rank. -/
theorem phase_parabolic_strict_max {r : ℕ} (hr : 0 < r) {a b₀ b : ℝ}
    (ha : 0 < a) (hne : b ≠ b₀) :
    (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2) (parabolicPoint a b)).re <
      (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2) (parabolicPoint a b₀)).re := by
  rw [phase_re_parabolicPoint r ha b₀ b, phase_re_parabolicPoint r ha b₀ b₀]
  exact mul_lt_mul_of_pos_left (parabolicPhase_strict_max ha hne) (Nat.cast_pos.mpr hr)

/-- On a finite arc the strict maximum supplies a uniform positive gap
outside any fixed neighborhood of its saddle parameter. -/
theorem exists_parabolicPhase_compact_gap {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (b₀ B : ℝ) :
    ∃ ε > 0, ∀ b ∈ Icc (-B) B, d ≤ |b - b₀| →
      parabolicPhase a b₀ b ≤ parabolicPhase a b₀ b₀ - ε := by
  let E : Set ℝ := Icc (-B) B ∩ {b | d ≤ |b - b₀|}
  have hE : IsCompact E := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  by_cases hne : E.Nonempty
  · have hc : Continuous (parabolicPhase a b₀) := continuous_iff_continuousAt.mpr
      (fun b => (hasDerivAt_parabolicPhase ha b₀ b).continuousAt)
    obtain ⟨b, hb, hmax⟩ := hE.exists_isMaxOn hne hc.continuousOn
    have hbne : b ≠ b₀ := by
      intro he
      have hbd : d ≤ |b - b₀| := hb.2
      rw [he, sub_self, abs_zero] at hbd
      linarith
    have hgap := parabolicPhase_strict_max ha hbne
    refine ⟨parabolicPhase a b₀ b₀ - parabolicPhase a b₀ b, sub_pos.mpr hgap, ?_⟩
    intro t ht htd
    have hm := hmax (show t ∈ E from ⟨ht, htd⟩)
    change parabolicPhase a b₀ t ≤ parabolicPhase a b₀ b at hm
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro b hb hbd
    exact (hne ⟨b, hb, hbd⟩).elim

end ThisWork
