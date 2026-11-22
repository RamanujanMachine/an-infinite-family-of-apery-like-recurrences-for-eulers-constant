module

public import ThisWork.HigherRank.LocalWindowIdentity
public import ThisWork.HigherRank.ParabolicCoordinates

/-! Proven local saddle data for every off-cut branch in arbitrary rank.
The construction has no assumed asymptotic expansion or moment limit. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric
open scoped Topology OnePoint

structure OffCutLocalData (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ) (θ : ℝ) where
  a : ℝ
  a_pos : 0 < a
  b : ℝ
  radius_eq : a ^ 2 + b ^ 2 = saddleScale r A z
  angle_eq : 2 * Real.arctan (b / a) = θ
  saddle_eq : parabolicPoint a b = (saddleScale r A z : ℂ) * Phase.rho θ
  radius : ℝ
  radius_pos : 0 < radius
  disk_slit : ball (parabolicPoint a b) radius ⊆ Complex.slitPlane
  family : CompactSaddleFamily r A z j (parabolicPoint a b) radius
  localData : family.LocalParabolicData (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I))

theorem exists_offCutLocalData {r : ℕ} (hr : 3 ≤ r) {A : Fin (r - 1) → ℝ} {z θ : ℝ}
    (hA : ∀ i, 0 < A i) (hz : 0 < z) (j : ℤ) (hθ : θ ∈ Ioo (-Real.pi) Real.pi)
    (hj : (r : ℝ) * θ = -2 * Real.pi * j) : Nonempty (OffCutLocalData r A z j θ) := by
  have hc := saddleScale_pos hA hz
  obtain ⟨a, ha, b, hscale, hangle, hpoint⟩ := exists_parabolic_coordinates hc hθ
  have hslit := parabolicPoint_mem_slitPlane ha b
  have hzero : limitingEquation r A z j (parabolicPoint a b) = 0 := by
    rw [limitingEquation_eq_phase (by omega : 0 < r) hA hz j hj (Complex.slitPlane_ne_zero hslit), hpoint]
    exact Phase.equation_saddle r hθ hc
  obtain ⟨d, hd, hdslit, ⟨S⟩⟩ := exists_compactSaddleFamily hr hA z j hslit hzero
  have hpositive : 0 < (S.phaseCoefficients 0 ∞ *
      (2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) ^ 2).re := by
    rw [S.parabolic_quadratic_coefficient ha]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) (Nat.cast_pos.mpr (show 0 < r by omega)))
  obtain ⟨D⟩ := S.exists_localParabolicData hpositive
  exact ⟨⟨a, ha, b, hscale, hangle, hpoint, d, hd, hdslit, S, D⟩⟩

namespace OffCutLocalData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z θ : ℝ} {j : ℤ} (D : OffCutLocalData r A z j θ)

theorem tangent_ne_zero : 2 * Complex.I * ((D.a : ℂ) + (D.b : ℂ) * Complex.I) ≠ 0 := by
  have hw : (D.a : ℂ) + (D.b : ℂ) * Complex.I ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith [D.a_pos]
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hw

theorem normalizedLocalMoment_tendsto (hr : 1 < r) (k : ℕ) :
    Tendsto (fun n : ℕ => D.localData.normalizedLocalMoment
      (largeScale r (n + D.localData.shift + D.family.firstIndex)) k n)
      atTop (𝓝 (((saddleScale r A z : ℂ) * Phase.rho θ) ^ k)) := by
  simpa only [D.saddle_eq] using D.localData.normalizedLocalMoment_tendsto hr D.tangent_ne_zero k

end OffCutLocalData
end ThisWork.HigherRank
