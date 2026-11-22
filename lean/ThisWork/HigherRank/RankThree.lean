module

public import ThisWork.HigherRank.Definitions

/-! Compatibility with the existing rank-three definitions. -/

@[expose] public section
namespace ThisWork.HigherRank

def branchIndex : ThisWork.Branch → ℤ
  | .one => 1
  | .two => -1
  | .three => 0

theorem branchIndex_twist (j : ThisWork.Branch) :
    2 * (Real.pi : ℂ) * Complex.I * branchIndex j = ThisWork.twist j := by
  cases j <;> simp only [branchIndex, ThisWork.twist, ThisWork.saddleAngle]
  all_goals push_cast; ring

theorem kernel_rank_three (A₁ A₂ z : ℝ) (j : ThisWork.Branch) (n : ℕ) (x : ℂ) :
    kernel 3 1 ![A₁, A₂] z (branchIndex j) n x =
      ThisWork.kernel A₁ A₂ z j n x := by
  simp only [kernel, Nat.reduceSub, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_one, one_mul, branchIndex_twist, ThisWork.kernel]
  ring

theorem branchIntegral_rank_three (A₁ A₂ z : ℝ) (j : ThisWork.Branch) (n : ℕ) :
    branchIntegral 3 1 ![A₁, A₂] z (branchIndex j) n =
      ThisWork.branchIntegral A₁ A₂ z j n := by
  funext k
  unfold branchIntegral ThisWork.branchIntegral
  simp only [kernel_rank_three, Nat.cast_one, one_mul]

end ThisWork.HigherRank
