module

public import ThisWork.Trajectory.ReferenceMoments
public import ThisWork.Trajectory.Definitions

/-! Independence from the common initial Mellin–Barnes state. -/

@[expose] public section

namespace ThisWork.Trajectory

open Polynomial

/-- The three initial states are independent at every positive real argument. -/
theorem initial_linearIndependent {z : ℝ} (hz : 0 < z) :
    LinearIndependent ℂ (fun j : Branch => ThisWork.branchIntegral 1 1 z j 0) := by
  let : Fintype Branch := Fintype.ofEquiv (Fin 3) Analytic.branchEquiv
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let L : ℂ[X] →ₗ[ℂ] ℂ := ∑ j, c j • originMoments hz j
  have hrec (P : ℂ[X]) : L (P * X ^ 3) =
      (z : ℂ) * L (P.comp (X - 1) * (X - 1) ^ 2) := by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simp_rw [originMoments_recurrence]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinit (k : Fin 3) : L (X ^ k.val) = 0 := by
    have hk := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    have hn : L ((-X) ^ k.val) = 0 := by
      simpa only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        originMoments_initial_component] using hk
    have he : ((-X) ^ k.val : ℂ[X]) = (-1 : ℂ) ^ k.val • (X ^ k.val) := by
      simp only [Polynomial.smul_eq_C_mul, map_pow, map_neg, map_one]
      rw [← mul_pow, neg_one_mul]
    rw [he, map_smul, smul_eq_mul] at hn
    exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero _ (by norm_num))
  have hL : L = 0 := functional_eq_zero_of_origin_recurrence L (z : ℂ) hrec hinit
  have hs : ∑ j, c j • (fun n => ThisWork.branchIntegral 1 1 z j n) = 0 := by
    funext n k
    have h := DFunLike.congr_fun hL (referencePolynomial n k.val)
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [branchIntegral_reference_eq_originMoments hz]
    calc
      ∑ j, c j * (Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
          originMoments hz j (referencePolynomial n k.val)) =
          Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
            ∑ j, c j * originMoments hz j (referencePolynomial n k.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [h, mul_zero]
  exact Fintype.linearIndependent_iff.mp
    (ThisWork.branchIntegral_linearIndependent (α₁ := 1) (α₂ := 1)
      (by norm_num) (by norm_num) hz) c hs

theorem branchIntegral_zero (m d : ℕ) (A₁ A₂ z : ℝ) (j : Branch) :
    branchIntegral m d A₁ A₂ z j 0 = ThisWork.branchIntegral 1 1 z j 0 := by
  funext k
  simp only [branchIntegral, ThisWork.branchIntegral, kernel, ThisWork.kernel,
    Nat.cast_zero, mul_zero, zero_add, zero_sub, pow_succ]

/-- Every trajectory has independent branch sequences: evaluation at zero
recovers the same independent initial states. -/
theorem branchIntegral_linearIndependent (m d : ℕ) (A₁ A₂ : ℝ) {z : ℝ} (hz : 0 < z) :
    LinearIndependent ℂ (fun j : Branch => branchIntegral m d A₁ A₂ z j) := by
  apply LinearIndependent.of_comp (LinearMap.proj 0)
  change LinearIndependent ℂ (fun j : Branch => branchIntegral m d A₁ A₂ z j 0)
  simpa only [branchIntegral_zero] using
    initial_linearIndependent hz

end ThisWork.Trajectory
