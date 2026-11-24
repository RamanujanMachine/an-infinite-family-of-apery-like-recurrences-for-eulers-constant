module

public import ThisWork.HigherRank.Definitions

/-! Exact reindexing for arbitrary rank and equal positive lower slopes. -/

@[expose] public section
namespace ThisWork.HigherRank

private theorem complex_slope_reindex {b : ℕ} (hm : 0 < b) (A : ℝ) (n : ℕ) :
    ((A / (b : ℝ) : ℝ) : ℂ) * (b * n : ℕ) = (A : ℂ) * n := by
  push_cast
  field_simp [show (b : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne']

theorem kernel_reindex {b : ℕ} (hm : 0 < b) (r : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ) (n : ℕ) (x : ℂ) :
    kernel r b A z j n x =
      kernel r 1 (fun i => A i / b) z j (b * n) x := by
  unfold kernel
  simp_rw [complex_slope_reindex hm]
  simp only [Nat.cast_one, one_mul, Nat.cast_mul]

theorem branchIntegral_reindex {b : ℕ} (hm : 0 < b) (r : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ) (n : ℕ) :
    branchIntegral r b A z j n =
      branchIntegral r 1 (fun i => A i / b) z j (b * n) := by
  funext k
  unfold branchIntegral
  simp_rw [kernel_reindex hm]
  simp only [Nat.cast_one, one_mul, Nat.cast_mul]

end ThisWork.HigherRank
