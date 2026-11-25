module

public import ThisWork.ReflectedRealWindow
public import ThisWork.ReflectedRealTails
public import ThisWork.ReflectedDeformation
public import ThisWork.FixedCompactBounds
public import ThisWork.BoundaryScales

/-! Positive real integral underlying the even-rank boundary branch. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable def reflectedRealIntegral (r b : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (n : ℕ) (right : ℝ) : ℝ :=
  ∫ x in Iic right, ‖reflectedKernel r b A z n (x : ℂ)‖

theorem norm_reflectedKernel_ofReal {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℝ} (hx : x < 1) :
    (‖reflectedKernel r b A z n (x : ℂ)‖ : ℂ) = reflectedKernel r b A z n (x : ℂ) := by
  have hp := reflectedKernel_real_pos hA b z n hx
  rw [reflectedKernel_ofReal] at hp ⊢
  rw [Complex.norm_of_nonneg (by simpa only [Complex.ofReal_re] using hp.le)]

theorem reflected_integral_eq_positive {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {right : ℝ} (hright : right < 1) :
    (∫ x in Iic right, reflectedKernel r b A z n (x : ℂ)) =
      (reflectedRealIntegral r b A z n right : ℂ) := by
  calc
    _ = ∫ x in Iic right, (‖reflectedKernel r b A z n (x : ℂ)‖ : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x hx
      exact (norm_reflectedKernel_ofReal hA b z n (hx.trans_lt hright)).symm
    _ = _ := integral_complex_ofReal

theorem uniform_reflectedKernel_real_window_upper {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z T right : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (hT : 0 < T) (hright : right < 1) (b : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, -(largeScale r n * T) ≤ x → x ≤ right →
      ‖reflectedKernel r b A z n (x : ℂ)‖ ≤ commonScale r b A z n *
        Real.exp ((r : ℝ) * saddleScale r A z * largeScale r n +
          C * (largeScale r n * smallParameter r n)) := by
  let K := Complex.ofReal '' Icc (-2 : ℝ) (max right (-2))
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hleft : ∀ w ∈ K, w.re < 1 := by
    rintro w ⟨x, hx, rfl⟩
    exact hx.2.trans_lt (max_lt hright (by norm_num))
  obtain ⟨B, hB, D, hD, hcompact⟩ := uniform_reflectedKernel_fixed_compact_bound
    (by omega : 0 < r) hA hz b hK hleft
  obtain ⟨C, hC, hwindow⟩ := uniform_log_norm_reflectedKernel_real_window hr hA hz hT b
  let E := B + D * (2 * ((r : ℝ) + 1))
  refine ⟨max C E, le_max_of_le_left hC, ?_⟩
  filter_upwards [hcompact, hwindow, eventually_ge_atTop (1 : ℕ)] with n hnK hnW hn1 x hx hxR
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have he : 0 ≤ largeScale r n * smallParameter r n :=
    mul_nonneg hR.le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hcs := commonScale_pos hA hz b n
  have hc := saddleScale_pos hA hz
  by_cases hx2 : x ≤ -2
  · let t := -x / largeScale r n
    have ht : 0 < t := div_pos (by linarith) hR
    have htT : t ≤ T := (div_le_iff₀ hR).mpr (by linarith)
    have hRt : largeScale r n * t = -x := by dsimp only [t]; field_simp
    have hxcast : -(largeScale r n : ℂ) * (t : ℂ) = (x : ℂ) := by
      rw [neg_mul, ← Complex.ofReal_mul, hRt, Complex.ofReal_neg, neg_neg]
    have hb := (abs_le.mp (hnW t ht htT (by linarith [hRt]))).2
    rw [hxcast] at hb
    have hphase : reflectedRealPhase (saddleScale r A z) t ≤ saddleScale r A z := by
      by_cases htC : t = saddleScale r A z
      · rw [htC, reflectedRealPhase_self (saddleScale_pos hA hz)]
      · exact (reflectedRealPhase_strict_max (saddleScale_pos hA hz) ht htC).le
    calc
      _ ≤ Real.exp (Real.log ‖reflectedKernel r b A z n (x : ℂ)‖) := Real.le_exp_log _
      _ ≤ Real.exp (Real.log (commonScale r b A z n) +
          ((r : ℝ) * saddleScale r A z * largeScale r n + max C E * (largeScale r n * smallParameter r n))) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hphase (mul_nonneg hR.le (Nat.cast_nonneg r)),
          mul_le_mul_of_nonneg_right (le_max_left C E) he])
      _ = _ := by rw [Real.exp_add, Real.exp_log hcs]
  · have hmem : (x : ℂ) ∈ K := ⟨x, ⟨by linarith, hxR.trans (le_max_left _ _)⟩, rfl⟩
    have hp := polynomial_le_exp_errorScale hr hn1 hB hD
    calc
      _ ≤ B * commonScale r b A z n * Real.exp (D * (1 + Real.log (n : ℝ))) := hnK _ hmem
      _ = commonScale r b A z n * (B * Real.exp (D * (1 + Real.log (n : ℝ)))) := by ring
      _ ≤ commonScale r b A z n * Real.exp (E * (largeScale r n * smallParameter r n)) :=
        mul_le_mul_of_nonneg_left hp hcs.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have hs : 0 ≤ (r : ℝ) * saddleScale r A z * largeScale r n := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (le_max_right C E) he])) hcs.le

end ThisWork
