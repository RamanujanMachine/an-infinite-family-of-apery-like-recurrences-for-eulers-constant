module

public import ThisWork.HigherRank.FullParabolicContour
public import ThisWork.HigherRank.OffCutGlobalMoments

/-! Exact recovery of the defining zero-center moment vector from the
full power-moment contour. Polynomial recentering is handled separately. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem scaledWeightedKernel_zero (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (n k : ℕ) (s : ℂ) :
    scaledWeightedKernel r 0 A z j n k s = (-(largeScale r n : ℂ)) ^ k *
      (s ^ k * kernel r 0 A z j n ((largeScale r n : ℂ) * s)) := by
  simp only [scaledWeightedKernel, Nat.cast_zero, zero_mul, zero_sub, ← neg_mul, mul_pow]
  ring

theorem eventually_zeroCenter_branchIntegral_eq_powerMoment {r : ℕ} (hr : 1 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {a B Y d : ℝ} (ha : 0 < a) (hB : 0 < B) (hY : 0 ≤ Y) (hd : 0 < d) (hda : d < a ^ 2)
    (hheight : B ^ 3 + 4 * a ^ 2 * B ≤ 4 * a * Y) :
    ∃ η > 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ < η → ∀ k : Fin r,
      branchIntegral r 0 A z j n k =
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (largeScale r n : ℂ) *
          (-(largeScale r n : ℂ)) ^ k.val * parabolicPowerMoment r 0 A z j n k.val a B δ := by
  obtain ⟨η, hη, hb⟩ := eventually_branchIntegral_eq_parabolic_with_tails hr hA 0 z j ha hB hY hd hda hheight
  refine ⟨η, hη, hb.mono (fun n hn δ hδ k => ?_)⟩
  rw [hn δ hδ k]
  let c := (-(largeScale r n : ℂ)) ^ k.val
  have hf : scaledWeightedKernel r 0 A z j n k.val =
      fun s => c * (s ^ k.val * kernel r 0 A z j n ((largeScale r n : ℂ) * s)) := by
    funext s
    exact scaledWeightedKernel_zero r A z j n k.val s
  rw [hf, parabolicArcIntegral_const_mul, integral_const_mul, integral_const_mul]
  simp only [parabolicArcIntegral, parabolicPowerMoment]
  ring

namespace OffCutLocalData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

theorem eventually_zeroCenter_branchIntegral_eq_powerMoment (hr : 1 < r)
    (hA : ∀ i, 0 < A i) {B : ℝ} (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, ∀ k : Fin r,
      branchIntegral r 0 A z j (D.index n) k =
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (largeScale r (D.index n) : ℂ) *
          (-(largeScale r (D.index n) : ℂ)) ^ k.val *
            parabolicPowerMoment r 0 A z j (D.index n) k.val D.a B (D.translation n) := by
  let Y := (B ^ 3 + 4 * D.a ^ 2 * B) / (4 * D.a) + 1
  have ha := D.a_pos
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hheight : B ^ 3 + 4 * D.a ^ 2 * B ≤ 4 * D.a * Y := by
    have hid : 4 * D.a * ((B ^ 3 + 4 * D.a ^ 2 * B) / (4 * D.a)) = B ^ 3 + 4 * D.a ^ 2 * B := by field_simp
    dsimp only [Y]
    nlinarith
  obtain ⟨η, hη, hb⟩ := HigherRank.eventually_zeroCenter_branchIntegral_eq_powerMoment hr hA z j
    D.a_pos hB hY (half_pos (sq_pos_of_pos ha)) (by nlinarith [sq_pos_of_pos ha] : D.a ^ 2 / 2 < D.a ^ 2) hheight
  filter_upwards [D.index_tendsto.eventually hb, D.eventually_translation_lt hη] with n hn hδ k
  exact hn (D.translation n) hδ k

end OffCutLocalData
end ThisWork.HigherRank
