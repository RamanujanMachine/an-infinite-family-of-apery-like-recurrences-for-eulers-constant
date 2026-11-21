module

public import ThisWork.Trajectory.KernelIdentities
public import ThisWork.Trajectory.HankelCongruence

/-! Absolute convergence and deformation for every trajectory `(m,m,m+d)`.
Only polynomial identities at a fixed index are used here; the degree is not
assumed bounded as the index grows. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter MeasureTheory Polynomial
open scoped Topology

noncomputable def weightPolynomial (m d n k : ℕ) : ℂ[X] :=
  (C ((m : ℂ) * n) - X) ^ k * ascPochhammer ℂ (d * n)

theorem weightedKernel_eq {z : ℝ} (hz : 0 < z) (m d : ℕ)
    (A₁ A₂ : ℝ) (j : Branch) (n k : ℕ) {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    ((m : ℂ) * n - x) ^ k * kernel m d A₁ A₂ z j n x =
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)) *
        (weightPolynomial m d n k).eval x *
          @Analytic.normalizedKernel ⟨z, hz⟩ A₁ A₂ j n x := by
  rw [kernel_eq_normalized_polynomial hz m d A₁ A₂ j n
    (Analytic.not_neg_nat_of_mem_slitPlane hx)]
  simp only [weightPolynomial, eval_mul, eval_pow, eval_sub, eval_C, eval_X]
  ring

theorem weighted_hankel_integrable {A₁ A₂ z r h : ℝ} (hz : 0 < z)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (m d : ℕ) (j : Branch) (n k : ℕ)
    (hr₀ : 0 < r) (hr : r < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h) :
    Analytic.HankelIntegrable r h
      (fun x => ((m : ℂ) * n - x) ^ k * kernel m d A₁ A₂ z j n x) := by
  let : PositiveArgument := ⟨z, hz⟩
  have hf := (Analytic.polynomial_hankel_integrable h₁ h₂ j n hr₀ hr hh
    (weightPolynomial m d n k)).const_mul
      (Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)))
  exact hf.congr (by linarith) (fun x hx => by
    simpa only [mul_assoc] using
      (weightedKernel_eq hz m d A₁ A₂ j n k
        (Analytic.hankelTrace_mem_slitPlane hr₀ (by linarith) hx)).symm)

/-- Evaluation on any admissible polygonal Hankel contour. -/
theorem weighted_hankel_eq_polynomial {z r h : ℝ} (hz : 0 < z)
    (m d : ℕ) (A₁ A₂ : ℝ) (j : Branch) (n k : ℕ) (hr : 0 < r) (hh : 0 < h) :
    hankelIntegral r h
        (fun x => ((m : ℂ) * n - x) ^ k * kernel m d A₁ A₂ z j n x) =
      Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)) *
        hankelIntegral r h (fun x => (weightPolynomial m d n k).eval x *
          @Analytic.normalizedKernel ⟨z, hz⟩ A₁ A₂ j n x) := by
  rw [← Analytic.hankelIntegral_const_mul]
  exact Analytic.hankelIntegral_congr hh.le (fun x hx => by
    simpa only [mul_assoc] using weightedKernel_eq hz m d A₁ A₂ j n k
      (Analytic.hankelTrace_mem_slitPlane hr hh hx))

/-- Fixed-index deformation for every polynomial moment of the unequal-slope kernel. -/
theorem weighted_hankel_eq {A₁ A₂ z r s h t : ℝ} (hz : 0 < z)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (m d : ℕ) (j : Branch) (n k : ℕ)
    (hr₀ : 0 < r) (hs₀ : 0 < s)
    (hr : r < min (A₁ * n + 1) (A₂ * n + 1))
    (hs : s < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    hankelIntegral r h (fun x => ((m : ℂ) * n - x) ^ k * kernel m d A₁ A₂ z j n x) =
      hankelIntegral s t (fun x => ((m : ℂ) * n - x) ^ k * kernel m d A₁ A₂ z j n x) := by
  rw [weighted_hankel_eq_polynomial hz m d A₁ A₂ j n k hr₀ (by linarith),
    weighted_hankel_eq_polynomial hz m d A₁ A₂ j n k hs₀ (by linarith)]
  exact congrArg (Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n)) * ·)
    (@Analytic.polynomial_hankel_eq ⟨z, hz⟩ A₁ A₂ r s h t h₁ h₂ j n hr₀ hs₀ hr hs hh ht
      (weightPolynomial m d n k))

theorem branchIntegral_eq_deformed {A₁ A₂ z r h : ℝ} (hz : 0 < z)
    (h₁ : 0 < A₁) (h₂ : 0 < A₂) (m d : ℕ) (j : Branch) (n : ℕ) (k : Fin 3)
    (hr₀ : 0 < r) (hr : r < min (A₁ * n + 1) (A₂ * n + 1)) (hh : 1 ≤ h) :
    branchIntegral m d A₁ A₂ z j n k = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      hankelIntegral r h (fun x => ((m : ℂ) * n - x) ^ k.val * kernel m d A₁ A₂ z j n x) := by
  have href : (1 / 2 : ℝ) < min (A₁ * n + 1) (A₂ * n + 1) := by
    apply lt_min <;> nlinarith [mul_nonneg h₁.le (Nat.cast_nonneg (α := ℝ) n),
      mul_nonneg h₂.le (Nat.cast_nonneg (α := ℝ) n)]
  exact congrArg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ·)
    (weighted_hankel_eq hz h₁ h₂ m d j n k.val (by norm_num) hr₀ href hr le_rfl hh)

end ThisWork.Trajectory
