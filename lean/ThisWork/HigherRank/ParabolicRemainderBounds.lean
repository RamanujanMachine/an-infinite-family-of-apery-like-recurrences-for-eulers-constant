module

public import ThisWork.HigherRank.ParabolicGap

/-! Uniform integrated bounds on compact parabolic pieces outside a fixed
saddle window. Every fixed power moment and the actual tangent are included. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem uniform_parabolic_power_remainder_bound {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (j : ℤ) (k : ℕ) {a auxB B h : ℝ} (ha : 0 < a) (hb : |auxB| ≤ B) (hh : 0 < h)
    (hscale : saddleScale r A z = a ^ 2 + auxB ^ 2)
    (hj : (r : ℝ) * (2 * Real.arctan (auxB / a)) = -2 * Real.pi * j) :
    ∃ η > 0, ∃ g > 0, ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ < η →
      ∀ u v : ℝ, (∀ t ∈ uIcc u v, t ∈ Icc (-B) B ∧ h ≤ |t - auxB|) →
        ‖∫ t in u..v, (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
          ((δ + parabolicPoint a t) ^ k *
            kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a t)))‖ ≤
          C * ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB))‖ *
            Real.exp (-g * largeScale r n) := by
  obtain ⟨d, hd, g, hg, hgap⟩ := uniform_kernel_parabolic_gap hr hA hz b j ha hb hh hscale hj
  have hB : 0 ≤ B := (abs_nonneg auxB).trans hb
  let M := a ^ 2 / 8 + a ^ 2 + B ^ 2
  let P := 2 * (a + B) * M ^ k
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨min d (a ^ 2 / 8), lt_min hd (by positivity), g, hg, P * (2 * B), by positivity, ?_⟩
  filter_upwards [hgap] with n hn δ hδ u v hpath
  have hδd := hδ.trans_le (min_le_left _ _)
  have hδa : ‖δ‖ ≤ a ^ 2 / 8 := (hδ.trans_le (min_le_right _ _)).le
  let K := ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB))‖ * Real.exp (-g * largeScale r n)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbound (t : ℝ) (ht : t ∈ uIoc u v) :
      ‖(2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
          ((δ + parabolicPoint a t) ^ k * kernel r b A z j n
            ((largeScale r n : ℂ) * (δ + parabolicPoint a t)))‖ ≤ P * K := by
    have ht' := hpath t (uIoc_subset_uIcc ht)
    have htB : |t| ≤ B := abs_le.mpr ht'.1
    have hamp := norm_translated_parabola_le hδa htB
    have hkernel := hn δ hδd t ht'.1 ht'.2
    rw [norm_mul (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) _,
      norm_mul ((δ + parabolicPoint a t) ^ k) _, norm_pow]
    calc
      _ ≤ (2 * (a + B)) * (M ^ k * K) :=
        mul_le_mul (norm_parabolic_tangent_le ha.le htB)
          (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hamp k) hkernel
            (norm_nonneg _) (pow_nonneg hM k))
          (mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _)) (by positivity)
      _ = _ := by dsimp only [P]; ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hlen : |v - u| ≤ 2 * B := by
    have hu := (hpath u left_mem_uIcc).1
    have hv := (hpath v right_mem_uIcc).1
    exact abs_le.mpr ⟨by linarith [hu.2, hv.1], by linarith [hu.1, hv.2]⟩
  exact hi.trans (by
    have hx := mul_le_mul_of_nonneg_left hlen (mul_nonneg hP hK)
    dsimp only [K] at hx
    nlinarith)

end ThisWork.HigherRank
