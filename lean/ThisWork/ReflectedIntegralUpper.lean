module

public import ThisWork.ReflectedIntegralBounds

/-! Integrating the finite-window and real-tail bounds. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

theorem integral_Iic_le_window_tail {f : ℝ → ℝ} {a auxB M : ℝ} (hab : a ≤ auxB)
    (hf : IntegrableOn f (Iic auxB)) (hwindow : ∀ x ∈ Icc a auxB, f x ≤ M)
    (htail : ∀ x ≤ a, f x ≤ M * Real.exp (x - a)) :
    (∫ x in Iic auxB, f x) ≤ M * (1 + auxB - a) := by
  have hleft := hf.mono_set (Iic_subset_Iic.mpr hab)
  have hg : IntegrableOn (fun x : ℝ => (M * Real.exp (-a)) * Real.exp x) (Iic a) :=
    (integrableOn_exp_Iic a).const_mul _
  have hb := setIntegral_mono_on hleft hg measurableSet_Iic (fun x hx => by
    convert htail x hx using 1
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring)
  rw [integral_const_mul, integral_exp_Iic, mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, mul_one] at hb
  have hint : IntervalIntegrable f volume a auxB := by
    apply IntegrableOn.intervalIntegrable
    exact hf.mono_set (by rw [uIcc_of_le hab]; exact Icc_subset_Iic_self)
  have hw := intervalIntegral.integral_mono_on hab hint (intervalIntegrable_const (c := M)) hwindow
  rw [intervalIntegral.integral_const, smul_eq_mul] at hw
  have hid := intervalIntegral.integral_Iic_sub_Iic hleft hf
  nlinarith

theorem reflectedRealIntegral_upper {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z right : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (hright : right < 1) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      reflectedRealIntegral r b A z n right ≤ commonScale r b A z n *
        Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n +
          C * (largeScale r n * smallParameter r n)) := by
  obtain ⟨T₀, hT₀, htail⟩ := uniform_reflected_real_tail_decay hr hA b z 1
  let T := max T₀ (|right| + 1)
  have hT : 1 ≤ T := hT₀.trans (le_max_left _ _)
  obtain ⟨C, hC, hwindow⟩ := uniform_reflectedKernel_real_window_upper hr hA hz
    (zero_lt_one.trans_le hT) hright b
  let D := 1 + |right| + T
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C + D + ((r : ℝ) + 1), by positivity, ?_⟩
  filter_upwards [htail, hwindow, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)] with n hnT hnW hR1 hn1
  let R := largeScale r n
  let e := smallParameter r n
  let M := commonScale r b A z n * Real.exp ((r : ℝ) * saddleScale r A z * R + C * (R * e))
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have he : 0 ≤ e := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hM : 0 ≤ M := (mul_pos (commonScale_pos hA hz b n) (Real.exp_pos _)).le
  have hab : -(R * T) ≤ right := by
    have ht := le_max_right T₀ (|right| + 1)
    have hp := mul_le_mul_of_nonneg_right hR1 (show 0 ≤ T by linarith)
    nlinarith [neg_le_abs right]
  have hi : IntegrableOn (fun x : ℝ => ‖reflectedKernel r b A z n (x : ℂ)‖) (Iic right) := by
    change Integrable (fun x : ℝ => ‖reflectedKernel r b A z n (x : ℂ)‖) (volume.restrict (Iic right))
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      (integrableOn_reflectedKernel_horizontal (by omega : 0 < r) hA half hrh b z n
        hright (y := 0) (by norm_num)).norm
  have hb := integral_Iic_le_window_tail hab hi
    (fun x hx => hnW x hx.1 hx.2) (M := M) (fun x hx => by
      let t := -x / R
      have ht : T ≤ t := (le_div_iff₀ hR).mpr (by nlinarith)
      have hid : -(R : ℂ) * (t : ℂ) = (x : ℂ) := by
        dsimp only [t]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
      have h := hnT T (le_max_left _ _) t ht
      change ‖reflectedKernel r b A z n (-(R : ℂ) * (t : ℂ))‖ ≤
        ‖reflectedKernel r b A z n (-(R : ℂ) * (T : ℂ))‖ * Real.exp (-1 * R * (t - T)) at h
      rw [hid] at h
      have hw : ‖reflectedKernel r b A z n (-(R : ℂ) * (T : ℂ))‖ ≤ M := by
        rw [neg_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg]
        exact hnW (-(R * T)) le_rfl hab
      have hexp : -1 * R * (t - T) = x - -(R * T) := by dsimp only [t]; field_simp; ring
      rw [hexp] at h
      exact h.trans (mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le))
  have hlen : 1 + right - -(R * T) ≤ D * R := by
    dsimp only [D]
    nlinarith [le_abs_self right, mul_le_mul_of_nonneg_right hR1 (show 0 ≤ 1 + |right| by positivity)]
  have hfactor : D * R ≤ Real.exp ((D + ((r : ℝ) + 1)) * (R * e)) := by
    have hlog := one_add_log_largeScale_le hr hn1
    have hone := one_le_errorScale hr hn1
    calc
      _ ≤ Real.exp D * R := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp D]) hR.le
      _ = Real.exp (D + Real.log R) := by rw [Real.exp_add D (Real.log R), Real.exp_log hR]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hone hD])
  calc
    _ ≤ M * (1 + right - -(R * T)) := hb
    _ ≤ M * (D * R) := mul_le_mul_of_nonneg_left hlen hM
    _ ≤ M * Real.exp ((D + ((r : ℝ) + 1)) * (R * e)) := mul_le_mul_of_nonneg_left hfactor hM
    _ = _ := by dsimp only [M]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end ThisWork
