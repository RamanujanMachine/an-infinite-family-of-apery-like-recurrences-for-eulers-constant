module

public import ThisWork.SaddleEquation

/-! The compact auxiliary parameter family used in Appendix A. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology

noncomputable def smallParameter (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ))

noncomputable def auxiliaryParameters (N : ℕ) : Set ℝ :=
  insert 0 (range (fun m : ℕ => smallParameter (m + N)))

theorem smallParameter_pos {n : ℕ} (hn : 0 < n) : 0 < smallParameter n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem smallParameter_tendsto : Tendsto smallParameter atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp tendsto_natCast_atTop_atTop

theorem isCompact_auxiliaryParameters (N : ℕ) : IsCompact (auxiliaryParameters N) :=
  (smallParameter_tendsto.comp (tendsto_add_atTop_nat N)).isCompact_insert_range

theorem zero_mem_auxiliaryParameters (N : ℕ) : (0 : ℝ) ∈ auxiliaryParameters N :=
  mem_insert 0 _

theorem smallParameter_mem_auxiliaryParameters {n N : ℕ} (hn : N ≤ n) :
    smallParameter n ∈ auxiliaryParameters N := by
  apply mem_insert_of_mem
  exact ⟨n - N, by simp only [Nat.sub_add_cancel hn]⟩

theorem auxiliaryParameters_eq (N : ℕ) :
    auxiliaryParameters N = {0} ∪ smallParameter '' Ici N := by
  ext z
  constructor
  · rintro (rfl | ⟨m, rfl⟩)
    · exact Or.inl (mem_singleton 0)
    · exact Or.inr ⟨m + N, Nat.le_add_left N m, rfl⟩
  · rintro (hz | ⟨n, hn, rfl⟩)
    · rw [mem_singleton_iff] at hz
      subst z
      exact zero_mem_auxiliaryParameters N
    · exact smallParameter_mem_auxiliaryParameters hn

theorem smallParameter_cube (n : ℕ) : smallParameter n ^ 3 = (n : ℝ)⁻¹ := by
  rw [smallParameter, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num
  rw [Real.rpow_neg_one]

theorem inv_smallParameter_sq (n : ℕ) : (smallParameter n ^ 2)⁻¹ = largeScale n := by
  rw [smallParameter, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  change ((n : ℝ) ^ (-(1 / 3 : ℝ) * (2 : ℕ)))⁻¹ = (n : ℝ) ^ (2 / 3 : ℝ)
  rw [show -(1 / 3 : ℝ) * (2 : ℕ) = -(2 / 3 : ℝ) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg n), inv_inv]

theorem largeScale_tendsto : Tendsto largeScale atTop atTop :=
  (tendsto_rpow_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).comp tendsto_natCast_atTop_atTop

theorem largeScale_div_nat {n : ℕ} (hn : 0 < n) : largeScale n / (n : ℝ) = smallParameter n := by
  rw [smallParameter, show -(1 / 3 : ℝ) = 2 / 3 - 1 by ring,
    Real.rpow_sub_one (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  rfl

theorem largeScale_div_nat_tendsto : Tendsto (fun n : ℕ => largeScale n / (n : ℝ)) atTop (𝓝 0) := by
  apply smallParameter_tendsto.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (largeScale_div_nat hn).symm

theorem inv_nat_le_smallParameter {n : ℕ} (hn : 1 ≤ n) : 1 / (n : ℝ) ≤ smallParameter n := by
  rw [smallParameter, one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

theorem inv_largeScale_le_smallParameter {n : ℕ} (hn : 1 ≤ n) : 1 / largeScale n ≤ smallParameter n := by
  rw [largeScale, one_div, ← Real.rpow_neg (Nat.cast_nonneg n), smallParameter]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

theorem largeScale_mul_smallParameter {n : ℕ} (hn : 0 < n) :
    largeScale n * smallParameter n = (n : ℝ) ^ (1 / 3 : ℝ) := by
  rw [largeScale, smallParameter, ← Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem one_add_log_largeScale_le {n : ℕ} (hn : 1 ≤ n) :
    1 + Real.log (largeScale n) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hp : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hl := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 3)
  have hR := log_largeScale (show 0 < n by omega)
  nlinarith

end ThisWork
