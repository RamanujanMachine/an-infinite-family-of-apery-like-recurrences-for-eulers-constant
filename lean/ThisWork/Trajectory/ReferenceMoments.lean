module

public import ThisWork.Trajectory.PolynomialMomentRecurrence

/-! Every moment of the reference integer trajectory is a polynomial moment of
its initial kernel. This permits independence to be checked at the initial state. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter MeasureTheory Polynomial
open scoped Topology

noncomputable def referencePolynomial (n k : ℕ) : ℂ[X] :=
  (C (n : ℂ) - X) ^ k * (ascPochhammer ℂ n).comp (1 - X) ^ 2

private theorem reference_kernel_polynomial (z : ℝ) (j : Branch) (n : ℕ) {x : ℂ}
    (hx : ∀ k : ℕ, 1 - x ≠ -k) :
    ThisWork.kernel 1 1 z j n x = Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
      (ascPochhammer ℂ n).eval (1 - x) ^ 2 * ThisWork.kernel 1 1 z j 0 x := by
  have hg : Complex.Gamma ((n : ℂ) - x + 1) =
      (ascPochhammer ℂ n).eval (1 - x) * Complex.Gamma (1 - x) := by
    simpa only [Nat.cast_one, one_mul, Nat.one_mul,
      show (n : ℂ) + (1 - x) = (n : ℂ) - x + 1 by ring] using Gamma_nat_shift 1 n hx
  simp only [ThisWork.kernel, Complex.ofReal_one, one_mul, Nat.cast_zero, mul_zero, zero_sub]
  rw [hg, show -x + 1 = (1 : ℂ) - x by ring,
    show (Real.log z : ℂ) * ((n : ℂ) - x) = (n : ℂ) * (Real.log z : ℂ) +
      (Real.log z : ℂ) * -x by ring, Complex.exp_add]
  ring

theorem branchIntegral_reference_eq_originMoments {z : ℝ} (hz : 0 < z)
    (j : Branch) (n : ℕ) (k : Fin 3) :
    ThisWork.branchIntegral 1 1 z j n k = Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
      originMoments hz j (referencePolynomial n k.val) := by
  have he : EqOn
      (fun x => ((n : ℂ) - x) ^ k.val * ThisWork.kernel 1 1 z j n x)
      (fun x => Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
        ((referencePolynomial n k.val).eval x * ThisWork.kernel 1 1 z j 0 x))
      (Analytic.hankelTrace (1 / 2) 1) := by
    intro x hx
    have hr : 0 < (1 - x).re := by
      have h := Analytic.hankelTrace_re_le hx
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    dsimp only
    rw [reference_kernel_polynomial z j n
      (Analytic.not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hr)))]
    simp_rw [referencePolynomial, eval_mul, eval_pow, eval_comp, eval_sub, eval_C, eval_one, eval_X]
    ring
  change Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
      (fun x => ((n : ℂ) - x) ^ k.val * ThisWork.kernel 1 1 z j n x) =
    Complex.exp ((n : ℂ) * (Real.log z : ℂ)) * (Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
      (fun x => (referencePolynomial n k.val).eval x * ThisWork.kernel 1 1 z j 0 x))
  rw [Analytic.hankelIntegral_congr (show (0 : ℝ) ≤ 1 by norm_num) he,
    Analytic.hankelIntegral_const_mul]
  ring

theorem originMoments_initial_component {z : ℝ} (hz : 0 < z) (j : Branch) (k : Fin 3) :
    originMoments hz j ((-X) ^ k.val) = ThisWork.branchIntegral 1 1 z j 0 k := by
  simp only [originMoments, LinearMap.coe_mk, AddHom.coe_mk, ThisWork.branchIntegral,
    Nat.cast_zero, zero_sub]
  change Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
      (fun x => ((-X) ^ k.val).eval x * ThisWork.kernel 1 1 z j 0 x) =
    Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
      (fun x => (-x) ^ k.val * ThisWork.kernel 1 1 z j 0 x)
  simp_rw [eval_pow, eval_neg, eval_X]

end ThisWork.Trajectory
