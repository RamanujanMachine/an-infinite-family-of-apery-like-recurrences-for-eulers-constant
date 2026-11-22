module

public import ThisWork.HigherRank.OffCutGlobalData

/-! Exponentially small full-contour remainder after removal of the actual
curved local Laplace window. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable def parabolicPowerMoment (r m : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n k : ℕ) (a B : ℝ) (δ : ℂ) : ℂ :=
  (∫ u in Iic (a ^ 2 - B ^ 2), (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I) ^ k *
    kernel r m A z j n ((largeScale r n : ℂ) * (δ + (u : ℂ) - ((2 * a * B : ℝ) : ℂ) * Complex.I))) +
  (∫ t in (-B)..B, (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
    ((δ + parabolicPoint a t) ^ k * kernel r m A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a t)))) -
  (∫ u in Iic (a ^ 2 - B ^ 2), (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I) ^ k *
    kernel r m A z j n ((largeScale r n : ℂ) * (δ + (u : ℂ) + ((2 * a * B : ℝ) : ℂ) * Complex.I)))

namespace OffCutLocalData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

theorem exists_full_moment_remainder_bound (hr : 3 ≤ r) (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (m k : ℕ) :
    ∃ B > 0, ∃ g > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖parabolicPowerMoment r m A z j (D.index n) k D.a B (D.translation n) -
        D.localData.localKernelMoment m (D.index n) (D.center n) k‖ ≤
        C * ‖kernel r m A z j (D.index n) ((largeScale r (D.index n) : ℂ) * D.center n)‖ *
          Real.exp (-g * largeScale r (D.index n)) := by
  let wp := D.localData.speed * D.localData.positive.cutoff
  let wm := D.localData.speed * D.localData.negative.cutoff
  have hwp : 0 < wp := mul_pos D.localData.speed_pos D.localData.positive.cutoff_mem.1
  have hwm : 0 < wm := mul_pos D.localData.speed_pos D.localData.negative.cutoff_mem.1
  let h := min wp wm
  have hh : 0 < h := lt_min hwp hwm
  obtain ⟨B, hB, hBb, dT, hdT, gT, hgT, CT, hCT, htail⟩ := uniform_parabolic_power_tail_bound
    hr hA hz m j k D.a_pos (by positivity : 0 < wp + wm + 1) D.radius_eq.symm D.angle_relation
  have hbB : |D.b| ≤ B := by linarith
  obtain ⟨dM, hdM, gM, hgM, CM, hCM, hmiddle⟩ := uniform_parabolic_power_remainder_bound
    hr hA hz m j k D.a_pos hbB hh D.radius_eq.symm D.angle_relation
  let g := min gT gM
  let d := min dT (min dM (D.a ^ 2 / 8))
  have hd : 0 < d := lt_min hdT (lt_min hdM (by have ha := D.a_pos; positivity))
  refine ⟨B, hB, g, lt_min hgT hgM, 2 * CT + 2 * CM, by positivity, ?_⟩
  filter_upwards [D.index_tendsto.eventually htail, D.index_tendsto.eventually hmiddle,
    D.index_tendsto.eventually (D.localData.eventually_localKernelMoment_eq_parabolic_window
      (by omega : 0 < r) hA D.a_pos m),
    D.index_tendsto.eventually (eventually_intervalIntegrable_parabolic_power (by omega : 0 < r) hA m z j D.a_pos),
    D.eventually_translation_lt hd,
    ((largeScale_tendsto (show 1 < r by omega)).comp D.index_tendsto).eventually
      (eventually_ge_atTop (1 : ℝ))] with n hnT hnM hnL hnI hnδ hR
  let R := largeScale r (D.index n)
  have hR1 : 1 ≤ R := hR
  have hR0 : 0 ≤ R := by linarith
  let δ := D.translation n
  let K := ‖kernel r m A z j (D.index n) ((R : ℂ) * D.center n)‖ * Real.exp (-g * R)
  let F : ℝ → ℂ := fun t => (2 * Complex.I * ((D.a : ℂ) + (t : ℂ) * Complex.I)) *
    ((δ + parabolicPoint D.a t) ^ k *
      kernel r m A z j (D.index n) ((R : ℂ) * (δ + parabolicPoint D.a t)))
  have hδT : ‖δ‖ < dT := hnδ.trans_le (min_le_left _ _)
  have hδM : ‖δ‖ < dM := hnδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : ‖δ‖ ≤ D.a ^ 2 / 8 := (hnδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hleft : -B ≤ D.b - wm := by linarith [neg_le_abs D.b]
  have hright : D.b + wp ≤ B := by linarith [le_abs_self D.b]
  have hwin : D.b - wm ≤ D.b + wp := by linarith
  have hlocal : D.localData.localKernelMoment m (D.index n) (D.center n) k =
      ∫ t in (D.b - wm)..(D.b + wp), F t := hnL (D.center n) hδa k
  have hi (u v : ℝ) : IntervalIntegrable F volume u v := hnI δ hδa k u v
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals (hi (-B) (D.b - wm)) (hi (D.b - wm) (D.b + wp))
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals (hi (-B) (D.b + wp)) (hi (D.b + wp) B)
  have hmidleft := hnM δ hδM (-B) (D.b - wm) (fun t ht => by
    rw [uIcc_of_le hleft] at ht
    refine ⟨⟨ht.1, by linarith [ht.2]⟩, ?_⟩
    have hm := min_le_right wp wm
    have habs := neg_le_abs (t - D.b)
    dsimp only [h] at *
    linarith [ht.2])
  have hmidright := hnM δ hδM (D.b + wp) B (fun t ht => by
    rw [uIcc_of_le hright] at ht
    refine ⟨⟨by linarith [ht.1], ht.2⟩, ?_⟩
    have hm := min_le_left wp wm
    have habs := le_abs_self (t - D.b)
    dsimp only [h] at *
    linarith [ht.1])
  have hcenter : δ + parabolicPoint D.a D.b = D.center n := D.translation_add_point n
  rw [hcenter] at hmidleft hmidright
  have hexpM : Real.exp (-gM * R) ≤ Real.exp (-g * R) := Real.exp_le_exp.mpr
    (by have hg := min_le_right gT gM; dsimp only [g]; nlinarith [mul_le_mul_of_nonneg_right hg hR0])
  have habsorbM {v : ℂ} (hv : ‖v‖ ≤ CM * ‖kernel r m A z j (D.index n) ((R : ℂ) * D.center n)‖ * Real.exp (-gM * R)) :
      ‖v‖ ≤ CM * K := by
    exact (hv.trans (mul_le_mul_of_nonneg_left hexpM (mul_nonneg hCM (norm_nonneg _)))).trans_eq (mul_assoc _ _ _)
  have hml : ‖∫ t in (-B)..(D.b - wm), F t‖ ≤ CM * K := habsorbM hmidleft
  have hmr : ‖∫ t in (D.b + wp)..B, F t‖ ≤ CM * K := habsorbM hmidright
  have hexpT : Real.exp (-gT * R) ≤ Real.exp (-g * R) := Real.exp_le_exp.mpr
    (by have hg := min_le_left gT gM; dsimp only [g]; nlinarith [mul_le_mul_of_nonneg_right hg hR0])
  have ht (e : ℝ) (he : e = 1 ∨ e = -1) :
      ‖∫ u in Iic (D.a ^ 2 - B ^ 2), (δ + (u : ℂ) + ((e * (2 * D.a * B) : ℝ) : ℂ) * Complex.I) ^ k *
        kernel r m A z j (D.index n) ((R : ℂ) *
          (δ + (u : ℂ) + ((e * (2 * D.a * B) : ℝ) : ℂ) * Complex.I))‖ ≤ CT * K := by
    have hb := hnT δ hδT e he
    rw [hcenter] at hb
    exact (hb.trans ((div_le_self (by positivity) hR1).trans
      (mul_le_mul_of_nonneg_left hexpT (mul_nonneg hCT.le (norm_nonneg _))))).trans_eq (mul_assoc _ _ _)
  have htl := ht (-1) (Or.inr rfl)
  have htr := ht 1 (Or.inl rfl)
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, one_mul] at htl htr
  let TL := ∫ u in Iic (D.a ^ 2 - B ^ 2), (δ + (u : ℂ) - ((2 * D.a * B : ℝ) : ℂ) * Complex.I) ^ k *
    kernel r m A z j (D.index n) ((R : ℂ) * (δ + (u : ℂ) - ((2 * D.a * B : ℝ) : ℂ) * Complex.I))
  let TR := ∫ u in Iic (D.a ^ 2 - B ^ 2), (δ + (u : ℂ) + ((2 * D.a * B : ℝ) : ℂ) * Complex.I) ^ k *
    kernel r m A z j (D.index n) ((R : ℂ) * (δ + (u : ℂ) + ((2 * D.a * B : ℝ) : ℂ) * Complex.I))
  have hdecomp : parabolicPowerMoment r m A z j (D.index n) k D.a B δ -
      D.localData.localKernelMoment m (D.index n) (D.center n) k =
      TL + (∫ t in (-B)..(D.b - wm), F t) + (∫ t in (D.b + wp)..B, F t) - TR := by
    rw [hlocal]
    change (TL + (∫ t in (-B)..B, F t) - TR) - _ = _
    linear_combination -hsplit₁ - hsplit₂
  change ‖parabolicPowerMoment r m A z j (D.index n) k D.a B δ - _‖ ≤ _
  rw [hdecomp]
  have h₀ := norm_add_le TL (∫ t in (-B)..(D.b - wm), F t)
  have h₁ := norm_add_le (TL + (∫ t in (-B)..(D.b - wm), F t)) (∫ t in (D.b + wp)..B, F t)
  have h₂ := norm_sub_le (TL + (∫ t in (-B)..(D.b - wm), F t) + (∫ t in (D.b + wp)..B, F t)) TR
  rw [mul_assoc]
  change _ ≤ (2 * CT + 2 * CM) * K
  nlinarith

end OffCutLocalData
end ThisWork.HigherRank
