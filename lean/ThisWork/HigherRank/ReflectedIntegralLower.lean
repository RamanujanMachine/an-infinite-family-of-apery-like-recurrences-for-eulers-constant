module

public import ThisWork.HigherRank.ReflectedIntegralBounds

/-! A positive window of width at least one gives the lower bound for
the full reflected real integral. No cancellation argument is required. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem reflectedRealPhase_near_max {c t e : ℝ} (hc : 0 < c)
    (ht : c ≤ t) (hte : t ≤ c + e) (hec : e ≤ c) :
    c - e ≤ reflectedRealPhase c t := by
  have ht0 : 0 < t := hc.trans_le ht
  have hl := Real.log_le_sub_one_of_pos (div_pos ht0 hc)
  have hid : Real.log (c / t) = -Real.log (t / c) := by
    rw [Real.log_div hc.ne' ht0.ne', Real.log_div ht0.ne' hc.ne']; ring
  have hm := mul_le_mul_of_nonneg_left hl hc.le
  have hdiv : c * (t / c - 1) = t - c := by field_simp
  rw [hdiv] at hm
  have hlog : c - t ≤ c * Real.log (c / t) := by rw [hid]; nlinarith
  have hp := mul_le_mul_of_nonneg_left hlog ht0.le
  have hsq : (t - c) ^ 2 ≤ c * e := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (by linarith : 0 ≤ c - (t - c)),
      mul_le_mul_of_nonneg_left (show t - c ≤ e by linarith) hc.le]
  unfold reflectedRealPhase
  nlinarith

theorem uniform_reflectedKernel_saddle_window_lower {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      saddleScale r A z ≤ t → t ≤ saddleScale r A z + smallParameter r n →
      commonScale r m A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n -
        C * (largeScale r n * smallParameter r n)) ≤
          ‖reflectedKernel r m A z n (-(largeScale r n : ℂ) * (t : ℂ))‖ := by
  let c := saddleScale r A z
  have hc : 0 < c := saddleScale_pos hA hz
  obtain ⟨C, hC, hb⟩ := uniform_log_norm_reflectedKernel_real_window hr hA hz (by positivity : 0 < 2 * c) m
  refine ⟨C + r, by positivity, ?_⟩
  filter_upwards [hb, (smallParameter_tendsto (show 0 < r by omega)).eventually
    (gt_mem_nhds hc), (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (2 / c)), eventually_ge_atTop (1 : ℕ)] with n hn he hRc hn1 t ht hte
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have hut : 2 ≤ largeScale r n * t := by
    have h := (div_le_iff₀ hc).mp hRc
    nlinarith [mul_le_mul_of_nonneg_left ht hR.le]
  have hb' := (abs_le.mp (hn t (hc.trans_le ht) (by linarith) hut)).1
  have hphase := reflectedRealPhase_near_max hc ht hte he.le
  have hne : 0 < ‖reflectedKernel r m A z n (-(largeScale r n : ℂ) * (t : ℂ))‖ :=
    norm_pos_iff.mpr (reflectedKernel_ne_zero_of_re_lt_one hA m z n (by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
        Complex.ofReal_im, neg_zero, zero_mul, sub_zero]; nlinarith))
  rw [← Real.exp_log (commonScale_pos hA hz m n), ← Real.exp_add, ← Real.exp_log hne]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hphase (mul_nonneg hR.le (Nat.cast_nonneg r))]

theorem reflectedRealIntegral_lower {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z right : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) (hright : right < 1) (m : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      commonScale r m A z n * Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n -
        C * (largeScale r n * smallParameter r n)) ≤ reflectedRealIntegral r m A z n right := by
  let c := saddleScale r A z
  have hc : 0 < c := saddleScale_pos hA hz
  obtain ⟨C, hC, hb⟩ := uniform_reflectedKernel_saddle_window_lower hr hA hz m
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, (largeScale_tendsto (show 1 < r by omega)).eventually
    (eventually_ge_atTop (|right| / c + 1)), eventually_ge_atTop (1 : ℕ)] with n hn hRc hn1
  let R := largeScale r n
  let e := smallParameter r n
  let L := commonScale r m A z n * Real.exp ((r : ℝ) * c * R - C * (R * e))
  have hR : 0 < R := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have he : 0 ≤ e := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hL : 0 ≤ L := (mul_pos (commonScale_pos hA hz m n) (Real.exp_pos _)).le
  have hright' : -(R * c) ≤ right := by
    have h := (div_le_iff₀ hc).mp (show |right| / c ≤ R by linarith)
    linarith [neg_le_abs right]
  have hab : -(R * (c + e)) ≤ -(R * c) := by nlinarith
  have hi : IntegrableOn (fun x : ℝ => ‖reflectedKernel r m A z n (x : ℂ)‖) (Iic right) := by
    change Integrable (fun x : ℝ => ‖reflectedKernel r m A z n (x : ℂ)‖) (volume.restrict (Iic right))
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      (integrableOn_reflectedKernel_horizontal (by omega : 0 < r) hA half hrh m z n
        hright (y := 0) (by norm_num)).norm
  have hisub := hi.mono_set (show Icc (-(R * (c + e))) (-(R * c)) ⊆ Iic right from
    fun x hx => hx.2.trans hright')
  have hsmall : L * volume.real (Icc (-(R * (c + e))) (-(R * c))) ≤
      ∫ x in Icc (-(R * (c + e))) (-(R * c)), ‖reflectedKernel r m A z n (x : ℂ)‖ := by
    apply setIntegral_ge_of_const_le_real measurableSet_Icc measure_Icc_lt_top.ne _ hisub
    intro x hx
    let t := -x / R
    have ht : c ≤ t := (le_div_iff₀ hR).mpr (by nlinarith [hx.2])
    have hte : t ≤ c + e := (div_le_iff₀ hR).mpr (by nlinarith [hx.1])
    have hid : -(R : ℂ) * (t : ℂ) = (x : ℂ) := by
      dsimp only [t]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hR.ne']
    have hh : L ≤ ‖reflectedKernel r m A z n (-(R : ℂ) * (t : ℂ))‖ := hn t ht hte
    rwa [hid] at hh
  rw [Real.volume_real_Icc_of_le hab] at hsmall
  have hwidth : -(R * c) - -(R * (c + e)) = R * e := by ring
  rw [hwidth] at hsmall
  have hmono := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun x => norm_nonneg _))
    (Filter.Eventually.of_forall (show ∀ x, x ∈ Icc (-(R * (c + e))) (-(R * c)) → x ∈ Iic right from
      fun x hx => hx.2.trans hright'))
  exact (by nlinarith [mul_le_mul_of_nonneg_left (one_le_errorScale hr hn1) hL] : L ≤ _).trans
    (hsmall.trans hmono)

end ThisWork.HigherRank
