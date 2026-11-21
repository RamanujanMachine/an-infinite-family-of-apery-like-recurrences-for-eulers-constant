module

public import ThisWork.Trajectory.Definitions
public import ThisWork.Normalization
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Exact polynomial reduction of the unequal-slope kernels.
The pole exclusion is necessary: Gamma's totalized values at poles do not
satisfy the polynomial shift identity when the shift crosses a pole. -/

@[expose] public section

namespace ThisWork.Trajectory

open Polynomial

/-- The extra Gamma factor is an ascending Pochhammer polynomial times Gamma. -/
theorem Gamma_nat_shift (d n : ℕ) {x : ℂ} (hx : ∀ k : ℕ, x ≠ -k) :
    Complex.Gamma ((d : ℂ) * n + x) =
      (ascPochhammer ℂ (d * n)).eval x * Complex.Gamma x := by
  simpa only [Nat.cast_mul, add_comm] using
    (div_eq_iff (Complex.Gamma_ne_zero hx)).mp
      (Complex.Gamma_add_nat_div_Gamma_eq (n := d * n) x hx)

/-- Reduction to the already formalized kernel, at each fixed index. -/
theorem kernel_eq_polynomial (m d : ℕ) (A₁ A₂ z : ℝ) (j : Branch)
    (n : ℕ) {x : ℂ} (hx : ∀ k : ℕ, x ≠ -k) :
    kernel m d A₁ A₂ z j n x =
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n - n)) *
        (ascPochhammer ℂ (d * n)).eval x * ThisWork.kernel A₁ A₂ z j n x := by
  unfold kernel ThisWork.kernel
  rw [Gamma_nat_shift d n hx, show (Real.log z : ℂ) * ((m : ℂ) * n - x) =
    (Real.log z : ℂ) * ((m : ℂ) * n - n) + (Real.log z : ℂ) * ((n : ℂ) - x) by ring,
    Complex.exp_add]
  ring

/-- A single polynomial factor reduces all fixed-index contour questions to the
existing normalized kernel. The scalar retains the full `z^(mn)` dependence. -/
theorem kernel_eq_normalized_polynomial {z : ℝ} (hz : 0 < z)
    (m d : ℕ) (A₁ A₂ : ℝ) (j : Branch) (n : ℕ) {x : ℂ}
    (hx : ∀ k : ℕ, x ≠ -k) :
    kernel m d A₁ A₂ z j n x =
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)) *
        (ascPochhammer ℂ (d * n)).eval x *
          @Analytic.normalizedKernel ⟨z, hz⟩ A₁ A₂ j n x := by
  have he : twist j * x + (Real.log z : ℂ) * ((m : ℂ) * n - x) =
      (Real.log z : ℂ) * ((m : ℂ) * n) + (twist j - (Real.log z : ℂ)) * x := by ring
  simp only [kernel, Analytic.normalizedKernel, Analytic.kernelTwist]
  rw [Gamma_nat_shift d n hx, mul_assoc, ← Complex.exp_add, he, Complex.exp_add]
  ring

theorem kernel_eq_gamma_quotient {z : ℝ} (hz : 0 < z)
    (m d : ℕ) (A₁ A₂ : ℝ) (j : Branch) (n : ℕ) {x : ℂ}
    (hx : ∀ k : ℕ, x ≠ -k) :
    kernel m d A₁ A₂ z j n x =
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)) *
        (Complex.Gamma ((d : ℂ) * n + x) / Complex.Gamma x *
          @Analytic.normalizedKernel ⟨z, hz⟩ A₁ A₂ j n x) := by
  rw [kernel_eq_normalized_polynomial hz m d A₁ A₂ j n hx,
    Gamma_nat_shift d n hx, mul_div_cancel_right₀ _ (Complex.Gamma_ne_zero hx)]
  ring

end ThisWork.Trajectory
