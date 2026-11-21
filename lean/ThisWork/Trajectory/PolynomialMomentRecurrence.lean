module

public import ThisWork.Trajectory.OriginMoments

/-! A triangular polynomial moment recurrence is determined by its first three moments. -/

@[expose] public section

namespace ThisWork.Trajectory

open Polynomial

private theorem functional_zero_of_degree (L : ℂ[X] →ₗ[ℂ] ℂ) {N : ℕ}
    (h : ∀ k < N, L (X ^ k) = 0) {P : ℂ[X]} (hP : P.natDegree < N) : L P = 0 := by
  rw [← sum_monomial_eq P, Polynomial.sum, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← smul_X_eq_monomial, map_smul, h k ((le_natDegree_of_mem_supp k hk).trans_lt hP), smul_zero]

theorem functional_eq_zero_of_origin_recurrence (L : ℂ[X] →ₗ[ℂ] ℂ) (z : ℂ)
    (hrec : ∀ P : ℂ[X], L (P * X ^ 3) = z * L (P.comp (X - 1) * (X - 1) ^ 2))
    (hinit : ∀ k : Fin 3, L (X ^ k.val) = 0) : L = 0 := by
  have hp : ∀ n : ℕ, L (X ^ n) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 3
      · exact hinit ⟨n, hn⟩
      · have hn₃ : 3 ≤ n := by omega
        have hr := hrec (X ^ (n - 3))
        rw [← pow_add, Nat.sub_add_cancel hn₃] at hr
        rw [pow_comp, X_comp, ← pow_add, show n - 3 + 2 = n - 1 by omega] at hr
        have hdeg : ((X - 1 : ℂ[X]) ^ (n - 1)).natDegree < n := by
          have hb := natDegree_pow_le (p := X - C (1 : ℂ)) (n := n - 1)
          rw [natDegree_X_sub_C, mul_one] at hb
          exact hb.trans_lt (by omega)
        rw [hr, functional_zero_of_degree L ih hdeg, mul_zero]
  apply LinearMap.ext
  intro P
  exact functional_zero_of_degree L (fun k _ => hp k) (Nat.lt_succ_self P.natDegree)

end ThisWork.Trajectory
