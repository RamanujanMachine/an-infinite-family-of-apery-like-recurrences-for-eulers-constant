module

public import ThisWork.Trajectory.OriginKernel

/-! Polynomial moments of the common initial Mellin–Barnes kernel. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter MeasureTheory Polynomial
open scoped Topology

theorem reference_polynomial_integrable {z r h : ℝ} (hz : 0 < z) (j : Branch) (n : ℕ)
    (P : ℂ[X]) (hr₀ : 0 < r) (hr : r < (n : ℝ) + 1) (hh : 1 ≤ h) :
    Analytic.HankelIntegrable r h (fun x => P.eval x * ThisWork.kernel 1 1 z j n x) := by
  let : PositiveArgument := ⟨z, hz⟩
  have hf := (Analytic.polynomial_hankel_integrable (A₁ := 1) (A₂ := 1)
    (by norm_num) (by norm_num) j n hr₀ (by simpa using hr) hh P).const_mul
      (Complex.exp ((n : ℂ) * (Real.log z : ℂ)))
  have he : (fun x => P.eval x * ThisWork.kernel 1 1 z j n x) =
      (fun x => Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
        (P.eval x * Analytic.normalizedKernel 1 1 j n x)) := by
    funext x
    rw [ThisWork.kernel_factor hz]
    ring
  rw [he]
  exact hf

noncomputable def originMoments {z : ℝ} (hz : 0 < z) (j : Branch) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun P := Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
    (fun x => P.eval x * ThisWork.kernel 1 1 z j 0 x)
  map_add' P Q := by
    simp only [eval_add, add_mul]
    rw [Analytic.hankelIntegral_add
      (reference_polynomial_integrable hz j 0 P (by norm_num) (by norm_num) le_rfl)
      (reference_polynomial_integrable hz j 0 Q (by norm_num) (by norm_num) le_rfl), mul_add]
  map_smul' a P := by
    simp only [Polynomial.smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_assoc]
    rw [Analytic.hankelIntegral_const_mul (1 / 2) 1
      (fun x => P.eval x * ThisWork.kernel 1 1 z j 0 x) a]
    ring

private theorem reference_polynomial_integral_factor {z : ℝ} (hz : 0 < z) (j : Branch)
    (n : ℕ) (P : ℂ[X]) (r h : ℝ) :
    hankelIntegral r h (fun x => P.eval x * ThisWork.kernel 1 1 z j n x) =
      Complex.exp ((n : ℂ) * (Real.log z : ℂ)) * hankelIntegral r h
        (fun x => P.eval x * @Analytic.normalizedKernel ⟨z, hz⟩ 1 1 j n x) := by
  have he : (fun x => P.eval x * ThisWork.kernel 1 1 z j n x) =
      (fun x => Complex.exp ((n : ℂ) * (Real.log z : ℂ)) *
        (P.eval x * @Analytic.normalizedKernel ⟨z, hz⟩ 1 1 j n x)) := by
    funext x
    rw [ThisWork.kernel_factor hz]
    ring
  rw [he, Analytic.hankelIntegral_const_mul]

private theorem reference_polynomial_hankel_eq {z r s h : ℝ} (hz : 0 < z)
    (j : Branch) (n : ℕ) (P : ℂ[X]) (hr₀ : 0 < r) (hs₀ : 0 < s)
    (hr : r < (n : ℝ) + 1) (hs : s < (n : ℝ) + 1) (hh : 1 ≤ h) :
    hankelIntegral r h (fun x => P.eval x * ThisWork.kernel 1 1 z j n x) =
      hankelIntegral s h (fun x => P.eval x * ThisWork.kernel 1 1 z j n x) := by
  rw [reference_polynomial_integral_factor hz j n P r h,
    reference_polynomial_integral_factor hz j n P s h]
  exact congrArg (Complex.exp ((n : ℂ) * (Real.log z : ℂ)) * ·)
    (@Analytic.polynomial_hankel_eq ⟨z, hz⟩ 1 1 r s h h (by norm_num) (by norm_num) j n
      hr₀ hs₀ (by simpa using hr) (by simpa using hs) hh hh P)

theorem originMoments_recurrence {z : ℝ} (hz : 0 < z) (j : Branch) (P : ℂ[X]) :
    originMoments hz j (P * X ^ 3) =
      (z : ℂ) * originMoments hz j (P.comp (X - 1) * (X - 1) ^ 2) := by
  let f : ℂ → ℂ := fun x => P.eval (x - 1) * ThisWork.kernel 1 1 z j 1 x
  have he : EqOn (fun x => P.eval x * x ^ 3 * ThisWork.kernel 1 1 z j 0 x)
      (fun x => f (x + 1)) (Analytic.hankelTrace (1 / 2) 1) := by
    intro x hx
    dsimp only [f]
    rw [origin_kernel_shift z j (Complex.slitPlane_ne_zero
      (Analytic.hankelTrace_mem_slitPlane (by norm_num) (by norm_num) hx)), add_sub_cancel_right]
    ring
  have ht := (Analytic.hankelIntegral_congr (show (0 : ℝ) ≤ 1 by norm_num) he).trans
    (Analytic.hankelIntegral_translate (1 / 2) 1 1 f)
  have hd := reference_polynomial_hankel_eq (r := 3 / 2) (s := 1 / 2) (h := 1)
    hz j 1 (P.comp (X - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
  simp_rw [eval_comp, eval_sub, eval_X, eval_one] at hd
  have hleft : hankelIntegral (1 / 2) 1
      (fun x => P.eval x * x ^ 3 * ThisWork.kernel 1 1 z j 0 x) = hankelIntegral (1 / 2) 1 f := by
    rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at ht
    exact ht.trans hd
  have he' : EqOn f (fun x => (z : ℂ) *
      (P.eval (x - 1) * (x - 1) ^ 2 * ThisWork.kernel 1 1 z j 0 x))
      (Analytic.hankelTrace (1 / 2) 1) := by
    intro x hx
    have hx₁ : 1 - x ≠ 0 := by
      intro heq
      have h := Analytic.hankelTrace_re_le hx
      have heq' := congrArg Complex.re heq
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at heq'
      linarith
    dsimp only [f]
    rw [origin_kernel_right hz j hx₁]
    ring
  have hright := Analytic.hankelIntegral_congr (show (0 : ℝ) ≤ 1 by norm_num) he'
  change Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
      (fun x => (P * X ^ 3).eval x * ThisWork.kernel 1 1 z j 0 x) =
    (z : ℂ) * (Analytic.cauchyFactor * hankelIntegral (1 / 2) 1
      (fun x => (P.comp (X - 1) * (X - 1) ^ 2).eval x * ThisWork.kernel 1 1 z j 0 x))
  simp_rw [eval_mul, eval_pow, eval_comp, eval_sub, eval_one, eval_X]
  rw [hleft, hright, Analytic.hankelIntegral_const_mul]
  ring

end ThisWork.Trajectory
