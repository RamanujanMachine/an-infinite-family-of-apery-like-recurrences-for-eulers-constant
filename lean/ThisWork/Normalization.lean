module

public import ThisWork.HankelLinearity

/-! Exact identities separating the common factor `z^n` from the z-dependent
Mellin–Barnes kernel. The normalized objects are internal to the analytic proof. -/

@[expose] public section

namespace ThisWork

open Set Filter
open scoped Topology

theorem kernel_eq_cpow {z : ℝ} (hz : 0 < z) (α₁ α₂ : ℝ) (j : Branch)
    (n : ℕ) (x : ℂ) :
    kernel α₁ α₂ z j n x = Complex.Gamma x ^ 3 *
      Complex.Gamma ((α₁ : ℂ) * n - x + 1) * Complex.Gamma ((α₂ : ℂ) * n - x + 1) *
      Complex.exp (twist j * x) * (z : ℂ) ^ ((n : ℂ) - x) := by
  rw [kernel, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne'),
    ← Complex.ofReal_log hz.le]

@[simp] theorem kernel_one (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (x : ℂ) :
    kernel α₁ α₂ 1 j n x = Complex.Gamma x ^ 3 *
      Complex.Gamma ((α₁ : ℂ) * n - x + 1) * Complex.Gamma ((α₂ : ℂ) * n - x + 1) *
      Complex.exp (twist j * x) := by
  simp [kernel]

theorem kernel_factor {z : ℝ} (hz : 0 < z) (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (x : ℂ) :
    kernel α₁ α₂ z j n x = Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
      @Analytic.normalizedKernel ⟨z, hz⟩ α₁ α₂ j n x := by
  have he : twist j * x + (Real.log z : ℂ) * ((n : ℂ) - x) =
      (n : ℂ) * (Real.log z : ℂ) + (twist j - (Real.log z : ℂ)) * x := by ring
  simp only [kernel, Analytic.normalizedKernel, Analytic.kernelTwist]
  rw [mul_assoc, ← Complex.exp_add, he, Complex.exp_add]
  ring

theorem branchIntegral_factor {z : ℝ} (hz : 0 < z) (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) :
    branchIntegral α₁ α₂ z j n = Complex.exp ((n : ℂ) * (Real.log z : ℂ)) •
      @Analytic.normalizedBranchIntegral ⟨z, hz⟩ α₁ α₂ j n := by
  let : PositiveArgument := ⟨z, hz⟩
  funext k
  unfold branchIntegral Analytic.normalizedBranchIntegral
  simp only [kernel_factor hz, Pi.smul_apply, smul_eq_mul]
  rw [show (fun x : ℂ => ((n : ℂ) - x) ^ k.val *
      (Complex.exp ((n : ℂ) * (Real.log z : ℂ)) * Analytic.normalizedKernel α₁ α₂ j n x)) =
      (fun x => Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
        (((n : ℂ) - x) ^ k.val * Analytic.normalizedKernel α₁ α₂ j n x)) by
    funext x
    ring]
  rw [Analytic.hankelIntegral_const_mul]
  ring

theorem norm_branchIntegral_factor {z : ℝ} (hz : 0 < z) (α₁ α₂ : ℝ)
    (j : Branch) (n : ℕ) :
    ‖branchIntegral α₁ α₂ z j n‖ = z ^ n *
      ‖@Analytic.normalizedBranchIntegral ⟨z, hz⟩ α₁ α₂ j n‖ := by
  rw [branchIntegral_factor hz, norm_smul]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.exp_nat_mul, Real.exp_log hz]

end ThisWork
