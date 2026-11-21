module

public import ThisWork.Trajectory.EqualSlopes
public import ThisWork.Recessiveness

/-! Strong recessiveness for every equal lower slope and symbolic `z > 0`.
Exact reindexing preserves the conclusion for all fixed combinations. -/

@[expose] public section
namespace ThisWork.Trajectory

open Filter
open scoped Topology

/-- The third integral is strongly recessive relative to every nontrivial
fixed combination of the two dominant equal-lower-slope branches. -/
theorem equal_stronglyRecessive {m : ℕ} (hm : 0 < m) {A₁ A₂ z : ℝ}
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    StronglyRecessiveInSpan (branchIntegral m 0 A₁ A₂ z) := by
  intro a ha
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hr : Tendsto (fun n : ℕ => m * n) atTop atTop := by
    refine tendsto_atTop.mpr (fun N => ?_)
    exact eventually_atTop.mpr ⟨N, fun n hn => hn.trans (Nat.le_mul_of_pos_left n hm)⟩
  have hc (n : ℕ) : dominantCombination (branchIntegral m 0 A₁ A₂ z) a n =
      dominantCombination (ThisWork.branchIntegral (A₁ / m) (A₂ / m) z) a (m * n) := by
    simp only [dominantCombination, branchIntegral_equal_reindex hm]
  obtain ⟨hnonzero, hdecay⟩ := ThisWork.branchIntegral_stronglyRecessive
    (div_pos h₁ hmR) (div_pos h₂ hmR) hz a ha
  refine ⟨?_, fun N => ?_⟩
  · filter_upwards [hr.eventually hnonzero] with n hn
    rwa [hc]
  · have hlim := ((hdecay N).comp hr).const_mul (((m : ℝ) ^ N)⁻¹)
    simp only [mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [] with n
    rw [branchIntegral_equal_reindex hm, hc]
    simp only [Function.comp_apply, Nat.cast_mul, mul_pow]
    field_simp [(pow_pos hmR N).ne']

end ThisWork.Trajectory
