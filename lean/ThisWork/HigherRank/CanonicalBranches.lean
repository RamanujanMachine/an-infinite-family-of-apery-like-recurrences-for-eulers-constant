module

public import ThisWork.HigherRank.OffCutIndependence

/-! A balanced set of integer Fourier labels, with precisely one boundary
label in even rank and no boundary label in odd rank. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set

def branchLabel (r : ℕ) (k : Fin r) : ℤ := (r / 2 : ℕ) - (k.val : ℤ)

noncomputable def branchAngle (r : ℕ) (k : Fin r) : ℝ :=
  -2 * Real.pi * (branchLabel r k : ℝ) / r

theorem branchLabel_injective (r : ℕ) : Function.Injective (branchLabel r) := by
  intro i j hij
  apply Fin.ext
  dsimp only [branchLabel] at hij
  omega

theorem branchAngle_relation {r : ℕ} (hr : 0 < r) (k : Fin r) :
    (r : ℝ) * branchAngle r k = -2 * Real.pi * (branchLabel r k : ℝ) := by
  dsimp only [branchAngle]
  field_simp [Nat.cast_ne_zero.mpr hr.ne']

theorem branchAngle_injective {r : ℕ} (hr : 0 < r) : Function.Injective (branchAngle r) := by
  intro i j hij
  apply branchLabel_injective r
  have h := congrArg (fun t => (r : ℝ) * t) hij
  rw [branchAngle_relation hr, branchAngle_relation hr] at h
  have he : (branchLabel r i : ℝ) = branchLabel r j := by nlinarith [Real.pi_pos]
  exact_mod_cast he

theorem branchAngle_mem_principal {r : ℕ} (hr : 0 < r) (k : Fin r)
    (hk : 2 * (r / 2) < r ∨ 0 < k.val) :
    branchAngle r k ∈ Ioo (-Real.pi) Real.pi := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hlow : -(r : ℝ) < 2 * ((r / 2 : ℕ) - (k.val : ℝ)) := by
    have hn : r < 2 * (r / 2) + 2 := by omega
    have hi : k.val < r := k.isLt
    have hint : -(r : ℤ) < 2 * ((r / 2 : ℕ) - (k.val : ℤ)) := by omega
    exact_mod_cast hint
  have hupp : 2 * ((r / 2 : ℕ) - (k.val : ℝ)) < (r : ℝ) := by
    have hn : 2 * (r / 2) ≤ r := by omega
    have hint : 2 * ((r / 2 : ℕ) - (k.val : ℤ)) < (r : ℤ) := by
      rcases hk with h | h <;> omega
    exact_mod_cast hint
  simp only [branchAngle, branchLabel, Int.cast_sub, Int.cast_natCast, mem_Ioo]
  constructor
  · apply (lt_div_iff₀ hr0).mpr
    nlinarith [mul_lt_mul_of_pos_left hupp Real.pi_pos]
  · apply (div_lt_iff₀ hr0).mpr
    nlinarith [mul_lt_mul_of_pos_left hlow Real.pi_pos]

theorem even_branchAngle_zero {r half : ℕ} (hr : 0 < r) (hrh : r = 2 * half) :
    branchAngle r ⟨0, hr⟩ = -Real.pi := by
  have hd : r / 2 = half := by omega
  simp only [branchAngle, branchLabel, hd, Nat.cast_zero, sub_zero, Int.cast_natCast]
  have hh : (half : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hrh]
  push_cast
  field_simp

end ThisWork.HigherRank
