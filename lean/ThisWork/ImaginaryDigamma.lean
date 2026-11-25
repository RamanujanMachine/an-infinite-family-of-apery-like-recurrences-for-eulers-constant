module

public import ThisWork.ImaginaryDigammaTools
public import ThisWork.Scales

/-! Quantitative digamma bounds at the arbitrary-rank small-parameter scale,
including neighborhoods crossing the imaginary axis. -/

@[expose] public section
namespace ThisWork

open Filter
open scoped Topology

theorem norm_digamma_sub_log_right_small {R ε η : ℝ} (hR : 0 < R)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hscale : 1 ≤ R * ε ^ 2) (hη : 0 < η)
    {w : ℂ} (hre : 0 ≤ w.re) (him : R * η ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w‖ ≤ (1 + 8 / η) * ε := by
  let N : ℕ := ⌈ε⁻¹⌉₊ + 2
  have hN2 : 2 ≤ N := by dsimp only [N]; omega
  have hNlo : ε⁻¹ ≤ (N : ℝ) - 1 := by
    have h := Nat.le_ceil ε⁻¹
    dsimp only [N]
    push_cast
    linarith
  have hNhi : (N : ℝ) ≤ 4 / ε := by
    have hc := Nat.ceil_lt_add_one (inv_pos.mpr hε).le
    apply (le_div_iff₀ hε).mpr
    dsimp only [N]
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hc hε, inv_mul_cancel₀ hε.ne']
  have hfirst : 1 / ((N : ℝ) - 1) ≤ ε := by
    have h := one_div_le_one_div_of_le (inv_pos.mpr hε) hNlo
    simpa only [one_div, inv_inv] using h
  have hRe : 1 / (R * ε) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hR hε)).mpr
    nlinarith [hscale]
  have hsecond : 2 * (N : ℝ) / |w.im| ≤ (8 / η) * ε := by
    calc
      _ ≤ 2 * (N : ℝ) / (R * η) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hR hη) him
      _ ≤ 2 * (4 / ε) / (R * η) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNhi (by norm_num)) (by positivity)
      _ = (8 / η) * (1 / (R * ε)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hRe (by positivity)
  have hb := Analytic.norm_digamma_sub_log_of_re_nonneg hre
    (abs_pos.mp ((mul_pos hR hη).trans_le him)) hN2
  exact hb.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

theorem norm_digamma_sub_log_im_small {R ε η : ℝ} (hR : 0 < R)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hscale : 1 ≤ R * ε ^ 2) (hη : 0 < η)
    {w : ℂ} (him : R * η ≤ |w.im|)
    (hexp : Real.exp (-2 * Real.pi * |w.im|) ≤ 1 / 2)
    (hexpR : Real.exp (-2 * Real.pi * |w.im|) ≤ 1 / R) :
    ‖Complex.digamma w - Complex.log w‖ ≤ (1 + 9 / η + 4 * Real.pi) * ε := by
  by_cases hre : 0 ≤ w.re
  · have hb := norm_digamma_sub_log_right_small hR hε hε1 hscale hη hre him
    have hc : 0 ≤ (1 / η + 4 * Real.pi) * ε := by positivity
    calc
      _ ≤ (1 + 8 / η) * ε := hb
      _ ≤ (1 + 8 / η) * ε + (1 / η + 4 * Real.pi) * ε := le_add_of_nonneg_right hc
      _ = _ := by ring
  have hinv : 1 / R ≤ ε := by
    apply (div_le_iff₀ hR).mpr
    have he : ε ^ 2 ≤ ε := by nlinarith
    simpa only [mul_comm] using hscale.trans (mul_le_mul_of_nonneg_left he hR.le)
  have hright : ‖Complex.digamma (1 - w) - Complex.log (1 - w)‖ ≤ (1 + 8 / η) * ε :=
    norm_digamma_sub_log_right_small hR hε hε1 hscale hη
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using him)
  have hfrac : 1 / |w.im| ≤ (1 / η) * ε := by
    calc
      _ ≤ 1 / (R * η) := one_div_le_one_div_of_le (mul_pos hR hη) him
      _ = (1 / η) * (1 / R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  have hcot : 4 * Real.pi * Real.exp (-2 * Real.pi * |w.im|) ≤ 4 * Real.pi * ε :=
    mul_le_mul_of_nonneg_left (hexpR.trans hinv) (by positivity)
  have hb := Analytic.norm_digamma_sub_log_reflection_im
    (abs_pos.mp ((mul_pos hR hη).trans_le him)) hexp
  exact hb.trans ((add_le_add (add_le_add hright hfrac) hcot).trans_eq (by ring))

/-- Quantitative convergence across the imaginary axis, at the small-parameter
rate needed for the logarithmic growth errors in every rank at least three. -/
theorem uniform_scaled_digamma_im_smallParameter {r : ℕ} (hr : 3 ≤ r)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, η ≤ |s.im| →
      ‖Complex.digamma ((largeScale r n : ℂ) * s) -
          Complex.log ((largeScale r n : ℂ) * s)‖ ≤
        (1 + 9 / η + 4 * Real.pi) * smallParameter r n := by
  filter_upwards [(largeScale_tendsto (show 1 < r by omega)).eventually
    (Analytic.eventually_exp_decay_bounds (show 0 < 2 * Real.pi * η by positivity)),
    eventually_ge_atTop (1 : ℕ)] with n hdec hn s hs
  have hR := hdec.1
  have hε : 0 < smallParameter r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have hden : largeScale r n * η ≤ |((largeScale r n : ℂ) * s).im| := by
    simpa [Complex.mul_im, abs_mul, abs_of_pos hR] using
      mul_le_mul_of_nonneg_left hs hR.le
  have he : Real.exp (-2 * Real.pi * |((largeScale r n : ℂ) * s).im|) ≤
      Real.exp (-(2 * Real.pi * η) * largeScale r n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 2 * Real.pi by positivity)]
  exact norm_digamma_sub_log_im_small hR hε (smallParameter_le_one r hn)
    (one_le_largeScale_mul_smallParameter_sq hr hn) hη hden
    (he.trans hdec.2.1) (he.trans hdec.2.2)

theorem uniform_scaled_digamma_region_smallParameter {r : ℕ} (hr : 3 ≤ r)
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, κ ≤ s.re ∨ η ≤ |s.im| →
      ‖Complex.digamma ((largeScale r n : ℂ) * s) -
          Complex.log ((largeScale r n : ℂ) * s)‖ ≤
        (2 / κ + 1 + 9 / η + 4 * Real.pi) * smallParameter r n := by
  filter_upwards [(largeScale_tendsto (show 1 < r by omega)).eventually
    (Analytic.uniform_scaled_digamma_right hκ), uniform_scaled_digamma_im_smallParameter hr hη,
    eventually_ge_atTop (1 : ℕ)] with n hright him hn s hs
  have hε : 0 < smallParameter r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  rcases hs with hre | hims
  · calc
      _ ≤ (2 / κ) / largeScale r n := hright.2 s hre
      _ ≤ (2 / κ) * smallParameter r n := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (inv_largeScale_le_smallParameter hr hn) (by positivity)
      _ ≤ (2 / κ) * smallParameter r n +
          (1 + 9 / η + 4 * Real.pi) * smallParameter r n := le_add_of_nonneg_right (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (1 + 9 / η + 4 * Real.pi) * smallParameter r n := him s hims
      _ ≤ (2 / κ) * smallParameter r n +
          (1 + 9 / η + 4 * Real.pi) * smallParameter r n := le_add_of_nonneg_left (by positivity)
      _ = _ := by ring

end ThisWork
