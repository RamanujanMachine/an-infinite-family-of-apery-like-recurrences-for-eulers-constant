module

public import ThisWork.Trajectory.AffineShift

/-! Exact and limiting saddle equations for the double-minimum Gamma kernel. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

noncomputable def kernelLogDerivative (d : ℕ) (A₁ A₂ z : ℝ)
    (j : Branch) (n : ℕ) (x : ℂ) : ℂ :=
  2 * Complex.digamma x + Complex.digamma ((d : ℂ) * n + x) -
    Complex.digamma ((A₁ : ℂ) * n - x + 1) -
    Complex.digamma ((A₂ : ℂ) * n - x + 1) + twist j - (Real.log z : ℂ)

noncomputable def exactSqrtEquation (d : ℕ) (A₁ A₂ z : ℝ)
    (j : Branch) (n : ℕ) (s : ℂ) : ℂ :=
  kernelLogDerivative d A₁ A₂ z j n ((sqrtScale n : ℂ) * s)

noncomputable def limitingSqrtEquation (d : ℕ) (A₁ A₂ z : ℝ)
    (j : Branch) (s : ℂ) : ℂ :=
  sqrtEquation (doubleSaddleScale d A₁ A₂ z) s + twist j

theorem log_doubleSaddleScale {d : ℕ} {A₁ A₂ z : ℝ} (hd : 0 < d)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    2 * Real.log (doubleSaddleScale d A₁ A₂ z) =
      Real.log A₁ + Real.log A₂ + Real.log z - Real.log d := by
  have h := congrArg Real.log (doubleSaddleScale_sq hd h₁ h₂ hz)
  simpa only [Real.log_pow, Nat.cast_ofNat,
    Real.log_div (mul_pos (mul_pos h₁ h₂) hz).ne' (Nat.cast_pos.mpr hd).ne',
    Real.log_mul (mul_pos h₁ h₂).ne' hz.ne', Real.log_mul h₁.ne' h₂.ne'] using h

theorem limitingSqrtEquation_eq_logs {d : ℕ} {A₁ A₂ z : ℝ} (hd : 0 < d)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (j : Branch) {s : ℂ} (hs : s ≠ 0) :
    limitingSqrtEquation d A₁ A₂ z j s =
      2 * Complex.log s + (Real.log d : ℂ) - (Real.log A₁ : ℂ) -
        (Real.log A₂ : ℂ) + twist j - (Real.log z : ℂ) := by
  have hc := doubleSaddleScale_pos hd h₁ h₂ hz
  have hdiv : Complex.log (s / (doubleSaddleScale d A₁ A₂ z : ℂ)) =
      Complex.log s - (Real.log (doubleSaddleScale d A₁ A₂ z) : ℂ) := by
    rw [show s / (doubleSaddleScale d A₁ A₂ z : ℂ) =
      ((doubleSaddleScale d A₁ A₂ z)⁻¹ : ℝ) * s by push_cast; ring,
      Complex.log_ofReal_mul (inv_pos.mpr hc) hs, Real.log_inv, Complex.ofReal_neg]
    ring
  have he : (2 : ℂ) * (Real.log (doubleSaddleScale d A₁ A₂ z) : ℂ) =
      (Real.log A₁ : ℂ) + (Real.log A₂ : ℂ) + (Real.log z : ℂ) - (Real.log d : ℂ) := by
    exact_mod_cast log_doubleSaddleScale hd h₁ h₂ hz
  unfold limitingSqrtEquation sqrtEquation
  rw [hdiv]
  linear_combination -he

end ThisWork.Trajectory
