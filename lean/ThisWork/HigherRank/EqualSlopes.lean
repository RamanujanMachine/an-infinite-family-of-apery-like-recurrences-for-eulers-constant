module

public import ThisWork.HigherRank.Definitions

/-! Exact reindexing for arbitrary rank and equal positive lower slopes. -/

@[expose] public section
namespace ThisWork.HigherRank

private theorem complex_slope_reindex {m : ℕ} (hm : 0 < m) (A : ℝ) (n : ℕ) :
    ((A / (m : ℝ) : ℝ) : ℂ) * (m * n : ℕ) = (A : ℂ) * n := by
  push_cast
  field_simp [show (m : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne']

theorem kernel_reindex {m : ℕ} (hm : 0 < m) (r : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ) (n : ℕ) (x : ℂ) :
    kernel r m A z j n x =
      kernel r 1 (fun i => A i / m) z j (m * n) x := by
  unfold kernel
  simp_rw [complex_slope_reindex hm]
  simp only [Nat.cast_one, one_mul, Nat.cast_mul]

theorem branchIntegral_reindex {m : ℕ} (hm : 0 < m) (r : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ) (n : ℕ) :
    branchIntegral r m A z j n =
      branchIntegral r 1 (fun i => A i / m) z j (m * n) := by
  funext k
  unfold branchIntegral
  simp_rw [kernel_reindex hm]
  simp only [Nat.cast_one, one_mul, Nat.cast_mul]

end ThisWork.HigherRank
