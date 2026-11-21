module

public import ThisWork.Trajectory.HankelTranslation
public import ThisWork.Trajectory.KernelIdentities
public import ThisWork.Lemma8

/-! Exact contiguous identities at the common initial kernel. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter MeasureTheory Polynomial
open scoped Topology

@[simp] theorem exp_twist (j : Branch) : Complex.exp (twist j) = 1 := by
  cases j
  · rw [twist_one, Complex.exp_two_pi_mul_I]
  · rw [twist_two, show -2 * (Real.pi : ℂ) * Complex.I = -(2 * (Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  · simp

theorem origin_kernel_shift (z : ℝ) (j : Branch) {x : ℂ} (hx : x ≠ 0) :
    ThisWork.kernel 1 1 z j 1 (x + 1) = x ^ 3 * ThisWork.kernel 1 1 z j 0 x := by
  simp only [ThisWork.kernel, Complex.ofReal_one, Nat.cast_one, Nat.cast_zero,
    one_mul, mul_zero, zero_sub]
  rw [show (1 : ℂ) - (x + 1) + 1 = -x + 1 by ring,
    show (1 : ℂ) - (x + 1) = -x by ring,
    show twist j * (x + 1) = twist j * x + twist j by ring,
    Complex.exp_add, exp_twist, mul_one, Complex.Gamma_add_one x hx]
  ring

theorem origin_kernel_right {z : ℝ} (hz : 0 < z) (j : Branch) {x : ℂ} (hx : 1 - x ≠ 0) :
    ThisWork.kernel 1 1 z j 1 x =
      (z : ℂ) * (1 - x) ^ 2 * ThisWork.kernel 1 1 z j 0 x := by
  simp only [ThisWork.kernel, Complex.ofReal_one, Nat.cast_one, Nat.cast_zero,
    one_mul, mul_zero, zero_sub]
  rw [Complex.Gamma_add_one (1 - x) hx,
    show (Real.log z : ℂ) * (1 - x) = (Real.log z : ℂ) + (Real.log z : ℂ) * -x by ring,
    Complex.exp_add, show Complex.exp (Real.log z : ℂ) = (z : ℂ) by
      rw [← Complex.ofReal_exp, Real.exp_log hz], show -x + 1 = (1 : ℂ) - x by ring]
  ring

end ThisWork.Trajectory
