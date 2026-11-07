module

public import ThisWork.Argument
public import ThisWork.NormalizedDefinitions
public import ThisWork.HankelPhase
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! Pole separation and holomorphy for the actual Mellin–Barnes kernels. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

noncomputable def kernelDomain (α₁ α₂ : ℝ) (n : ℕ) : Set ℂ :=
  Complex.slitPlane ∩ {x | x.re < min (α₁ * n + 1) (α₂ * n + 1)}

theorem isOpen_kernelDomain (α₁ α₂ : ℝ) (n : ℕ) : IsOpen (kernelDomain α₁ α₂ n) :=
  Complex.isOpen_slitPlane.inter (isOpen_lt Complex.continuous_re continuous_const)

theorem not_neg_nat_of_mem_slitPlane {x : ℂ} (hx : x ∈ Complex.slitPlane) (m : ℕ) :
    x ≠ -(m : ℂ) := by
  rintro rfl
  simp [Complex.mem_slitPlane_iff] at hx
  exact not_lt_of_ge (Nat.cast_nonneg m) hx

theorem kernelDomain_right_re_pos {α₁ α₂ : ℝ} {n : ℕ} {x : ℂ}
    (hx : x ∈ kernelDomain α₁ α₂ n) :
    0 < ((α₁ : ℂ) * n - x + 1).re ∧ 0 < ((α₂ : ℂ) * n - x + 1).re := by
  have h := lt_min_iff.mp (show x.re < min (α₁ * n + 1) (α₂ * n + 1) from by
    simpa only [Set.mem_ofPred_eq] using hx.2)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re]
  constructor <;> linarith

theorem referenceContour_mem_kernelDomain {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (n : ℕ) {x : ℂ} (hx : x ∈ hankelTrace (1 / 2) 1) : x ∈ kernelDomain α₁ α₂ n := by
  refine ⟨hankelTrace_mem_slitPlane (by norm_num) (by norm_num) hx, ?_⟩
  have hr := hankelTrace_re_le hx
  change x.re < min (α₁ * n + 1) (α₂ * n + 1)
  apply lt_min_iff.mpr
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Holomorphy is proved for the actual Gamma-product normalizedKernel, with both pole
families excluded explicitly. -/
theorem differentiableOn_kernel [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) :
    DifferentiableOn ℂ (normalizedKernel α₁ α₂ j n) (kernelDomain α₁ α₂ n) := by
  intro x hx
  have hleft : DifferentiableAt ℂ Complex.Gamma x :=
    Complex.differentiableAt_Gamma x (not_neg_nat_of_mem_slitPlane hx.1)
  have hright := kernelDomain_right_re_pos hx
  have harg₁ : DifferentiableAt ℂ (fun t : ℂ => (α₁ : ℂ) * n - t + 1) x := by fun_prop
  have harg₂ : DifferentiableAt ℂ (fun t : ℂ => (α₂ : ℂ) * n - t + 1) x := by fun_prop
  have hg₁ := (Complex.hasDerivAt_Gamma_of_re_pos hright.1).differentiableAt.comp x harg₁
  have hg₂ := (Complex.hasDerivAt_Gamma_of_re_pos hright.2).differentiableAt.comp x harg₂
  have he : DifferentiableAt ℂ (fun t : ℂ => Complex.exp (kernelTwist j * t)) x := by fun_prop
  have h := (((hleft.pow 3).fun_mul hg₁).fun_mul hg₂).fun_mul he
  change DifferentiableWithinAt ℂ (fun t => Complex.Gamma t ^ 3 *
    Complex.Gamma ((α₁ : ℂ) * n - t + 1) * Complex.Gamma ((α₂ : ℂ) * n - t + 1) *
      Complex.exp (kernelTwist j * t)) (kernelDomain α₁ α₂ n) x
  simpa only [Pi.pow_def, Function.comp_def] using h.differentiableWithinAt

end ThisWork.Analytic
