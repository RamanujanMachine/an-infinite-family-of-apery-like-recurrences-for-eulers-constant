module

public import ThisWork.HigherRank.EvenBoundaryBranch
public import ThisWork.HigherRank.BranchCenterGrowth

/-! The growth estimate for every original branch in every rank at least three. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter
open scoped Topology

theorem rho_neg_pi : Phase.rho (-Real.pi) = -1 := by
  simp only [Phase.rho, Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem branch_hasLogNormGrowth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (k : Fin r) :
    HasLogNormGrowth r (commonScale r b A z)
      (-(r : ℝ) * saddleScale r A z * (Phase.rho (branchAngle r k)).re)
      (branchIntegral r b A z (branchLabel r k)) := by
  by_cases hcut : 2 * (r / 2) = r ∧ k.val = 0
  · have hθ : branchAngle r k = -Real.pi := by
      have hk : k = ⟨0, by omega⟩ := Fin.ext hcut.2
      rw [hk]
      exact even_branchAngle_zero (by omega : 0 < r) hcut.1.symm
    have hg := (evenBoundary_zeroCenter_hasLogNormGrowth hr hA hz (r / 2) hcut.1.symm).recenter_branch hr hA hz b
    simpa only [branchLabel, hcut.2, Nat.cast_zero, sub_zero, hθ, rho_neg_pi,
      Complex.neg_re, Complex.one_re, mul_neg_one, neg_mul, neg_neg] using hg
  · have hk : 2 * (r / 2) < r ∨ 0 < k.val := by omega
    exact offCut_hasLogNormGrowth hr hA hz b (branchLabel r k)
      (branchAngle_mem_principal (by omega : 0 < r) k hk) (branchAngle_relation (by omega : 0 < r) k)

end ThisWork.HigherRank
