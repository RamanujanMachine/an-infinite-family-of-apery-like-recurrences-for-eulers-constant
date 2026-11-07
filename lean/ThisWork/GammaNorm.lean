module

public import ThisWork.Argument
public import ThisWork.LogNorm
public import ThisWork.DigammaBound

/-! Quantitative bounds for the logarithmic norm of Gamma in the right half-plane. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

noncomputable def stirlingMain (z : ℂ) : ℂ := z * (Complex.log z - 1)

noncomputable def gammaNormError (z : ℂ) : ℝ := Real.log ‖Complex.Gamma z‖ - (stirlingMain z).re

theorem hasDerivAt_stirlingMain {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt stirlingMain (Complex.log z) z := by
  have h := (hasDerivAt_id z).fun_mul ((Complex.hasDerivAt_log hz).sub_const 1)
  convert h using 1
  · rfl
  · simp only [id_eq, one_mul, mul_inv_cancel₀ (Complex.slitPlane_ne_zero hz), sub_add_cancel]

theorem hasDerivAt_gammaLogNorm_comp {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (ht : 0 < (γ t).re) :
    HasDerivAt (fun u => Real.log ‖Complex.Gamma (γ u)‖) (v * Complex.digamma (γ t)).re t := by
  have hΓ : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
    fun z hz => (Complex.differentiableAt_Gamma z
      (not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hz)))).differentiableWithinAt
  exact hasDerivAt_log_norm_comp (isOpen_lt continuous_const Complex.continuous_re) hΓ
    (fun _ hz => Complex.Gamma_ne_zero_of_re_pos hz) hγ ht

theorem hasDerivAt_gammaNormError_comp {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (ht : 0 < (γ t).re) :
    HasDerivAt (fun u => gammaNormError (γ u))
      (v * (Complex.digamma (γ t) - Complex.log (γ t))).re t := by
  have hm := Neuschel.hasDerivAt_primitive_comp
    (hasDerivAt_stirlingMain (Complex.mem_slitPlane_iff.mpr (Or.inl ht))) hγ
  convert (hasDerivAt_gammaLogNorm_comp hγ ht).fun_sub
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hm) using 1
  · rfl
  · simp only [Complex.reCLM_apply, mul_sub, Complex.sub_re]

theorem abs_gammaNormError_vertical_sub {a b : ℝ} (ha : 2 ≤ a) :
    |gammaNormError ((a : ℂ) + (b : ℂ) * Complex.I) - gammaNormError (a : ℂ)| ≤ 2 * |b| / a := by
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => gammaNormError ((a : ℂ) + (v : ℂ) * Complex.I))
      (Complex.I * (Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I) -
        Complex.log ((a : ℂ) + (u : ℂ) * Complex.I))).re u := by
    apply hasDerivAt_gammaNormError_comp
    · simpa only [id_eq, one_mul] using
        (((hasDerivAt_id (u : ℂ)).mul_const Complex.I).const_add (a : ℂ)).comp_ofReal
    · simpa using (show 0 < a by linarith)
  have hb (u : ℝ) : ‖(Complex.I * (Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I) -
      Complex.log ((a : ℂ) + (u : ℂ) * Complex.I))).re‖ ≤ 2 / a := by
    calc
      _ ≤ ‖Complex.I * (Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I) -
          Complex.log ((a : ℂ) + (u : ℂ) * Complex.I))‖ := by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
      _ = ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I) -
          Complex.log ((a : ℂ) + (u : ℂ) * Complex.I)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 2 / a := by simpa using norm_digamma_sub_log_le_two_div (s := (a : ℂ) + (u : ℂ) * Complex.I) (by simpa using ha)
  have h := (convex_uIcc (0 : ℝ) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hb u) left_mem_uIcc right_mem_uIcc
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero, Real.norm_eq_abs,
    div_mul_eq_mul_div] using h

theorem abs_gammaNormError_real_sub_two {a : ℝ} (ha : 2 ≤ a) :
    |gammaNormError (a : ℂ) - gammaNormError 2| ≤ 2 * (Real.log a - Real.log 2) := by
  have ha0 : 0 < a := by linarith
  have hlog : Real.log 2 ≤ Real.log a := Real.log_le_log (by norm_num) ha
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => gammaNormError (Real.exp v : ℂ))
      (((Real.exp u : ℝ) : ℂ) * (Complex.digamma (Real.exp u : ℂ) - Complex.log (Real.exp u : ℂ))).re u :=
    hasDerivAt_gammaNormError_comp (γ := fun v : ℝ => (Real.exp v : ℂ))
      (Real.hasDerivAt_exp u).ofReal_comp (by simpa only [Complex.ofReal_re] using Real.exp_pos u)
  have hb (u : ℝ) (hu : Real.log 2 ≤ u) :
      ‖(((Real.exp u : ℝ) : ℂ) * (Complex.digamma (Real.exp u : ℂ) - Complex.log (Real.exp u : ℂ))).re‖ ≤ 2 := by
    have hexp : 2 ≤ Real.exp u := by
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
    apply (show ‖(((Real.exp u : ℝ) : ℂ) * (Complex.digamma (Real.exp u : ℂ) -
      Complex.log (Real.exp u : ℂ))).re‖ ≤
      ‖((Real.exp u : ℝ) : ℂ) * (Complex.digamma (Real.exp u : ℂ) - Complex.log (Real.exp u : ℂ))‖
      from by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _).trans
    rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos u).le]
    calc
      _ ≤ Real.exp u * (2 / Real.exp u) := mul_le_mul_of_nonneg_left
        (norm_digamma_sub_log_le_two_div (s := (Real.exp u : ℂ))
          (by simpa only [Complex.ofReal_re] using hexp)) (Real.exp_pos u).le
      _ = 2 := by field_simp
  have h := (convex_Icc (Real.log 2) (Real.log a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) (fun u hu => hb u hu.1)
    (show Real.log 2 ∈ Icc (Real.log 2) (Real.log a) from ⟨le_rfl, hlog⟩)
    (show Real.log a ∈ Icc (Real.log 2) (Real.log a) from ⟨hlog, le_rfl⟩)
  simpa only [Real.exp_log ha0, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hlog), Complex.ofReal_ofNat] using h

/-- A coarse sector-uniform Stirling estimate for the actual Gamma function,
derived by integrating the digamma bound rather than assuming Stirling. -/
theorem abs_gammaNormError_right {z : ℂ} (hz : 2 ≤ z.re) :
    |gammaNormError z| ≤ |gammaNormError 2| + 2 * Real.log z.re + 2 * |z.im| / z.re := by
  have hv := abs_gammaNormError_vertical_sub (b := z.im) hz
  rw [Complex.re_add_im] at hv
  have hr := abs_gammaNormError_real_sub_two hz
  have htri₁ := abs_add_le (gammaNormError z - gammaNormError (z.re : ℂ)) (gammaNormError (z.re : ℂ))
  rw [sub_add_cancel] at htri₁
  have htri₂ := abs_add_le (gammaNormError (z.re : ℂ) - gammaNormError 2) (gammaNormError 2)
  rw [sub_add_cancel] at htri₂
  linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

end ThisWork.Analytic
