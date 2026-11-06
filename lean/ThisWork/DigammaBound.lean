module

public import ThisWork.GammaLogDerivative
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Quantitative right-half-plane bounds from Gauss' digamma limit. -/

public section

namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

/-- A telescoping majorant for the derivative error on successive unit intervals. -/
theorem inv_sq_le_telescope {a : ℝ} (ha : 1 < a) (k : ℕ) :
    1 / (a + k) ^ 2 ≤ 1 / (a + k - 1) - 1 / (a + k) := by
  have h₀ : 0 < a + k - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have h₁ : 0 < a + k := by linarith
  have he : 1 / (a + k - 1) - 1 / (a + k) = 1 / ((a + k - 1) * (a + k)) := by
    field_simp
    ring
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos h₀ h₁) (by nlinarith)

theorem sum_inv_sq_le {a : ℝ} (ha : 1 < a) (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (a + (k : ℝ)) ^ 2) ≤ 1 / (a - 1) := by
  have hbound := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => inv_sq_le_telescope ha k)
  have heq : (fun k : ℕ => 1 / (a + (k : ℝ) - 1) - 1 / (a + (k : ℝ))) =
      (fun k : ℕ => 1 / (a - 1 + (k : ℝ)) - 1 / (a - 1 + ((k + 1 : ℕ) : ℝ))) := by
    funext k
    push_cast
    congr 2 <;> ring
  rw [show (∑ k ∈ Finset.range n, (1 / (a + (k : ℝ) - 1) - 1 / (a + (k : ℝ)))) =
      ∑ k ∈ Finset.range n, (1 / (a - 1 + (k : ℝ)) - 1 / (a - 1 + ((k + 1 : ℕ) : ℝ))) from
        Finset.sum_congr rfl (fun k _ => congrFun heq k), Finset.sum_range_sub'] at hbound
  exact hbound.trans (by
    simp only [Nat.cast_zero, add_zero]
    exact sub_le_self _ (one_div_nonneg.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])))

theorem add_real_mem_slitPlane {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    s + (t : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  simpa only [Complex.add_re, Complex.ofReal_re] using add_pos_of_pos_of_nonneg hs ht

theorem resolvent_unit_error_le {s : ℂ} (hs : 0 < s.re) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (k : ℝ) ((k : ℝ) + 1)) :
    ‖(s + (k : ℂ))⁻¹ - (s + (t : ℂ))⁻¹‖ ≤ 1 / (s.re + (k : ℝ)) ^ 2 := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have ht0 : 0 ≤ t := hk.trans ht.1
  have hknz : s + (k : ℂ) ≠ 0 := shifted_ne_zero_of_re_pos hs k
  have htnz : s + (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero (add_real_mem_slitPlane hs ht0)
  have heq : (s + (k : ℂ))⁻¹ - (s + (t : ℂ))⁻¹ =
      ((t - (k : ℝ) : ℝ) : ℂ) / ((s + (k : ℂ)) * (s + (t : ℂ))) := by
    push_cast
    field_simp
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_of_nonneg (sub_nonneg.mpr ht.1)]
  have hn₁ : s.re + (k : ℝ) ≤ ‖s + (k : ℂ)‖ := by
    simpa only [Complex.add_re, Complex.natCast_re] using Complex.re_le_norm (s + (k : ℂ))
  have hn₂ : s.re + (k : ℝ) ≤ ‖s + (t : ℂ)‖ :=
    (add_le_add (le_refl s.re) ht.1).trans (by simpa only [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm (s + (t : ℂ)))
  have ha : 0 < s.re + (k : ℝ) := add_pos_of_pos_of_nonneg hs hk
  have hden : (s.re + (k : ℝ)) ^ 2 ≤ ‖s + (k : ℂ)‖ * ‖s + (t : ℂ)‖ := by
    rw [pow_two]
    exact mul_le_mul hn₁ hn₂ ha.le (norm_nonneg _)
  calc
    (t - (k : ℝ)) / (‖s + (k : ℂ)‖ * ‖s + (t : ℂ)‖) ≤
        1 / (‖s + (k : ℂ)‖ * ‖s + (t : ℂ)‖) :=
      div_le_div_of_nonneg_right (by linarith [ht.2]) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 1 / (s.re + (k : ℝ)) ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos ha) hden

theorem hasDerivAt_log_add_real {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => Complex.log (s + (u : ℂ))) (s + (t : ℂ))⁻¹ t := by
  have h := (Complex.hasDerivAt_log (add_real_mem_slitPlane hs ht)).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_add s)
  simpa only [Function.comp_def, id_eq, mul_one] using h.comp_ofReal

theorem continuousOn_resolvent {s : ℂ} (hs : 0 < s.re) {u v : ℝ} (hu : 0 ≤ u) :
    ContinuousOn (fun t : ℝ => (s + (t : ℂ))⁻¹) (Icc u v) := by
  apply (continuous_const.add Complex.continuous_ofReal).continuousOn.inv₀
  exact fun t ht => Complex.slitPlane_ne_zero (add_real_mem_slitPlane hs (hu.trans ht.1))

theorem integral_resolvent {s : ℂ} (hs : 0 < s.re) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ t in u..v, (s + (t : ℂ))⁻¹) = Complex.log (s + (v : ℂ)) - Complex.log (s + (u : ℂ)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
  · exact fun t ht => (hasDerivAt_log_add_real hs (hu.trans ht.1)).continuousAt.continuousWithinAt
  · exact fun t ht => hasDerivAt_log_add_real hs (hu.trans ht.1.le)
  · exact (continuousOn_resolvent hs hu).intervalIntegrable_of_Icc huv

theorem resolvent_log_unit_error_le {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖(s + (k : ℂ))⁻¹ - (Complex.log (s + (k : ℂ) + 1) - Complex.log (s + (k : ℂ)))‖ ≤
      1 / (s.re + (k : ℝ)) ^ 2 := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hi := (continuousOn_resolvent hs hk).intervalIntegrable_of_Icc (μ := volume) hkk
  have he : (∫ t in (k : ℝ)..(k : ℝ) + 1, ((s + (k : ℂ))⁻¹ - (s + (t : ℂ))⁻¹)) =
      (s + (k : ℂ))⁻¹ - (Complex.log (s + (k : ℂ) + 1) - Complex.log (s + (k : ℂ))) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, integral_resolvent hs hk hkk]
    simp [Complex.ofReal_add, Complex.ofReal_natCast, add_assoc]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht =>
    resolvent_unit_error_le hs k (show t ∈ Icc (k : ℝ) ((k : ℝ) + 1) from by
      rw [uIoc_of_le hkk] at ht
      exact ⟨ht.1.le, ht.2⟩))
  rw [he] at h
  simpa only [add_sub_cancel_left, abs_one, mul_one] using h

theorem resolvent_log_sum_error_le {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, (s + (k : ℂ))⁻¹) -
      (Complex.log (s + (n : ℂ)) - Complex.log s)‖ ≤ 1 / (s.re - 1) := by
  have hlogs : (∑ k ∈ Finset.range n,
      (Complex.log (s + (k : ℂ) + 1) - Complex.log (s + (k : ℂ)))) =
      Complex.log (s + (n : ℂ)) - Complex.log s := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, Nat.cast_zero, add_zero] using
      Finset.sum_range_sub (fun k : ℕ => Complex.log (s + (k : ℂ))) n
  rw [← hlogs, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k _ =>
    resolvent_log_unit_error_le (zero_lt_one.trans hs) k)).trans (sum_inv_sq_le hs n))

theorem log_nat_shift_sub_tendsto (s : ℂ) :
    Tendsto (fun n : ℕ => Complex.log ((n + 1 : ℕ) : ℂ) - Complex.log (s + ((n + 2 : ℕ) : ℂ)))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1))
  have hv : Tendsto (fun n : ℕ => (1 : ℂ) + (s + 1) / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero, mul_zero, add_zero,
      div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 : ℂ))).add
        (((Complex.continuous_ofReal.tendsto 0).comp hi).const_mul (s + 1))
  have hl : Tendsto (fun n : ℕ => Complex.log (1 + (s + 1) / ((n + 1 : ℕ) : ℂ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.log_one] using
      (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp hv
  have hlneg : Tendsto (fun n : ℕ => -Complex.log (1 + (s + 1) / ((n + 1 : ℕ) : ℂ))) atTop (𝓝 0) := by
    simpa only [neg_zero] using hl.neg
  apply hlneg.congr'
  filter_upwards [hv.eventually (isOpen_ne.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num))] with n hn
  have hn0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have he : s + ((n + 2 : ℕ) : ℂ) =
      (((n + 1 : ℕ) : ℝ) : ℂ) * (1 + (s + 1) / ((n + 1 : ℕ) : ℂ)) := by
    rw [Complex.ofReal_natCast]
    field_simp
    push_cast
    ring
  have hlog : Complex.log ((n + 1 : ℕ) : ℂ) = (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) :=
    (Complex.ofReal_log hr.le).symm
  rw [he, Complex.log_ofReal_mul hr hn, hlog]
  ring

/-- A quantitative digamma estimate on the right half-plane. This is the
analytic estimate needed to control the finite-`n` saddle equation. -/
theorem norm_digamma_sub_log_le {s : ℂ} (hs : 1 < s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 1 / (s.re - 1) := by
  have hlim : Tendsto (fun n : ℕ =>
      (∑ k ∈ Finset.range (n + 2), (s + (k : ℂ))⁻¹) -
        (Complex.log (s + ((n + 2 : ℕ) : ℂ)) - Complex.log s))
      atTop (𝓝 (Complex.log s - Complex.digamma s)) := by
    have h := ((log_nat_shift_sub_tendsto s).sub
      (digamma_eq_gauss_limit (zero_lt_one.trans hs))).add_const (Complex.log s)
    have h' : Tendsto (fun n : ℕ =>
        Complex.log ((n + 1 : ℕ) : ℂ) - Complex.log (s + ((n + 2 : ℕ) : ℂ)) -
          (Complex.log ((n + 1 : ℕ) : ℂ) - ∑ k ∈ Finset.range (n + 2), (s + (k : ℂ))⁻¹) + Complex.log s)
        atTop (𝓝 (Complex.log s - Complex.digamma s)) := by
      simpa only [zero_sub, neg_add_eq_sub] using h
    exact h'.congr' (Eventually.of_forall (fun n => by ring))
  have h := le_of_tendsto (continuous_norm.tendsto _ |>.comp hlim)
    (Eventually.of_forall (fun n : ℕ => resolvent_log_sum_error_le hs (n + 2)))
  simpa only [norm_sub_rev] using h

theorem norm_digamma_sub_log_le_two_div {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 2 / s.re := by
  apply (norm_digamma_sub_log_le (show 1 < s.re by linarith)).trans
  rw [div_le_div_iff₀ (show 0 < s.re - 1 by linarith) (show 0 < s.re by linarith)]
  linarith

theorem norm_log_add_one_sub_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.log (s + 1) - Complex.log s‖ ≤ 1 / s.re := by
  have he := integral_resolvent hs (u := 0) (v := 1) le_rfl zero_le_one
  simp only [Complex.ofReal_zero, add_zero, Complex.ofReal_one] at he
  rw [← he]
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1, ‖(s + (t : ℂ))⁻¹‖ ≤ 1 / s.re := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have hnt : s.re ≤ ‖s + (t : ℂ)‖ :=
      (show s.re ≤ s.re + t by linarith [ht.1]).trans
        (by simpa only [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm (s + (t : ℂ)))
    simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hs hnt
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb

end ThisWork
