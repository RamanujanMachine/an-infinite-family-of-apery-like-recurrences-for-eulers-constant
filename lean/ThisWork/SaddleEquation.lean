module

public import ThisWork.Argument
public import ThisWork.PoleFree
public import ThisWork.ScaledDigamma

/-! The exact saddle equation of the original Gamma-product normalizedKernel. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology

noncomputable def largeScale (n : ℕ) : ℝ := (n : ℝ) ^ (2 / 3 : ℝ)

noncomputable def kernelLogDerivative [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (x : ℂ) : ℂ :=
  3 * Complex.digamma x - Complex.digamma ((α₁ : ℂ) * n - x + 1) -
    Complex.digamma ((α₂ : ℂ) * n - x + 1) + kernelTwist j

noncomputable def exactSaddleEquation [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) (s : ℂ) : ℂ :=
  kernelLogDerivative α₁ α₂ j n ((largeScale n : ℂ) * s)

/-- This is an identity for the actual Gamma product. It does not use a
principal logarithm of Gamma, whose branch cuts would be unsuitable here. -/
theorem logDeriv_kernel [PositiveArgument] {α₁ α₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ kernelDomain α₁ α₂ n) :
    logDeriv (normalizedKernel α₁ α₂ j n) x = kernelLogDerivative α₁ α₂ j n x := by
  let g₀ : ℂ → ℂ := fun z => Complex.Gamma z ^ 3
  let g₁ : ℂ → ℂ := fun z => Complex.Gamma ((α₁ : ℂ) * n - z + 1)
  let g₂ : ℂ → ℂ := fun z => Complex.Gamma ((α₂ : ℂ) * n - z + 1)
  let g₃ : ℂ → ℂ := fun z => Complex.exp (kernelTwist j * z)
  have hright := kernelDomain_right_re_pos hx
  have hleftPole := not_neg_nat_of_mem_slitPlane hx.1
  have hrightPole₁ := not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hright.1))
  have hrightPole₂ := not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hright.2))
  have hleft := Complex.differentiableAt_Gamma x hleftPole
  have ha₁ : HasDerivAt (fun z : ℂ => (α₁ : ℂ) * n - z + 1) (-1) x := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using
      ((hasDerivAt_const x ((α₁ : ℂ) * n)).sub (hasDerivAt_id x)).add_const 1
  have ha₂ : HasDerivAt (fun z : ℂ => (α₂ : ℂ) * n - z + 1) (-1) x := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using
      ((hasDerivAt_const x ((α₂ : ℂ) * n)).sub (hasDerivAt_id x)).add_const 1
  have hd₀ : DifferentiableAt ℂ g₀ x := hleft.pow 3
  have hd₁ : DifferentiableAt ℂ g₁ x :=
    (Complex.differentiableAt_Gamma _ hrightPole₁).comp x ha₁.differentiableAt
  have hd₂ : DifferentiableAt ℂ g₂ x :=
    (Complex.differentiableAt_Gamma _ hrightPole₂).comp x ha₂.differentiableAt
  have he₃ := ((hasDerivAt_id x).const_mul (kernelTwist j)).cexp
  have hd₃ : DifferentiableAt ℂ g₃ x := by simpa only [id_eq] using he₃.differentiableAt
  have hn₀ : g₀ x ≠ 0 := pow_ne_zero 3 (Complex.Gamma_ne_zero hleftPole)
  have hn₁ : g₁ x ≠ 0 := Complex.Gamma_ne_zero hrightPole₁
  have hn₂ : g₂ x ≠ 0 := Complex.Gamma_ne_zero hrightPole₂
  have hn₃ : g₃ x ≠ 0 := Complex.exp_ne_zero _
  have hprod : logDeriv (fun z => g₀ z * g₁ z * g₂ z * g₃ z) x =
      logDeriv g₀ x + logDeriv g₁ x + logDeriv g₂ x + logDeriv g₃ x := by
    rw [logDeriv_fun_mul (f := fun z => g₀ z * g₁ z * g₂ z) (g := g₃) x
      (mul_ne_zero (mul_ne_zero hn₀ hn₁) hn₂) hn₃ ((hd₀.fun_mul hd₁).fun_mul hd₂) hd₃,
      logDeriv_fun_mul (f := fun z => g₀ z * g₁ z) (g := g₂) x
        (mul_ne_zero hn₀ hn₁) hn₂ (hd₀.fun_mul hd₁) hd₂,
      logDeriv_fun_mul (f := g₀) (g := g₁) x hn₀ hn₁ hd₀ hd₁]
  have hlog₀ : logDeriv g₀ x = 3 * Complex.digamma x := by
    simpa only [g₀, Nat.cast_ofNat, Complex.digamma_def] using logDeriv_fun_pow hleft 3
  have hlog₁ : logDeriv g₁ x = -Complex.digamma ((α₁ : ℂ) * n - x + 1) := by
    simpa only [neg_one_mul] using ha₁.logDeriv_Gamma hrightPole₁
  have hlog₂ : logDeriv g₂ x = -Complex.digamma ((α₂ : ℂ) * n - x + 1) := by
    simpa only [neg_one_mul] using ha₂.logDeriv_Gamma hrightPole₂
  have hlog₃ : logDeriv g₃ x = kernelTwist j := by
    rw [logDeriv_apply]
    change deriv (fun z => Complex.exp (kernelTwist j * z)) x / Complex.exp (kernelTwist j * x) = _
    have he : deriv (fun z => Complex.exp (kernelTwist j * z)) x = Complex.exp (kernelTwist j * x) * kernelTwist j := by
      simpa only [id_eq, mul_one] using he₃.deriv
    rw [he]
    exact mul_div_cancel_left₀ _ hn₃
  change logDeriv (fun z => g₀ z * g₁ z * g₂ z * g₃ z) x = _
  rw [hprod, hlog₀, hlog₁, hlog₂, hlog₃]
  simp only [kernelLogDerivative, sub_eq_add_neg]

theorem kernel_ne_zero [PositiveArgument] {α₁ α₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ kernelDomain α₁ α₂ n) : normalizedKernel α₁ α₂ j n x ≠ 0 := by
  have hright := kernelDomain_right_re_pos hx
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero 3 (Complex.Gamma_ne_zero (not_neg_nat_of_mem_slitPlane hx.1)))
    (Complex.Gamma_ne_zero_of_re_pos hright.1)) (Complex.Gamma_ne_zero_of_re_pos hright.2))
    (Complex.exp_ne_zero _)

theorem kernelLogDerivative_eq_zero_iff [PositiveArgument] {α₁ α₂ : ℝ} (j : Branch) (n : ℕ) {x : ℂ}
    (hx : x ∈ kernelDomain α₁ α₂ n) :
    kernelLogDerivative α₁ α₂ j n x = 0 ↔ deriv (normalizedKernel α₁ α₂ j n) x = 0 := by
  rw [← logDeriv_kernel j n hx, logDeriv_apply, div_eq_zero_iff]
  simp only [kernel_ne_zero j n hx, or_false]

theorem largeScale_pos {n : ℕ} (hn : 0 < n) : 0 < largeScale n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem log_largeScale {n : ℕ} (hn : 0 < n) :
    3 * Real.log (largeScale n) = 2 * Real.log (n : ℝ) := by
  rw [largeScale, Real.log_rpow (Nat.cast_pos.mpr hn)]
  ring

theorem limitingEquation_eq_logs [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) {s : ℂ} (hs : s ≠ 0) :
    limitingEquation j (saddleScale α₁ α₂) s =
      3 * Complex.log s - (Real.log α₁ : ℂ) - (Real.log α₂ : ℂ) + kernelTwist j := by
  let c := saddleScale α₁ α₂
  have hc : 0 < c := saddleScale_pos h₁ h₂
  have hlogc := log_saddleScale h₁ h₂
  have hcast : (3 : ℂ) * (Real.log c : ℂ) = (Real.log α₁ : ℂ) + (Real.log α₂ : ℂ) + (Real.log PositiveArgument.value : ℂ) := by
    exact_mod_cast hlogc
  have hdiv : Complex.log (s / (c : ℂ)) = Complex.log s - (Real.log c : ℂ) := by
    rw [show s / (c : ℂ) = ((c⁻¹ : ℝ) : ℂ) * s from by push_cast; ring,
      Complex.log_ofReal_mul (inv_pos.mpr hc) hs, Real.log_inv, Complex.ofReal_neg]
    ring
  change 3 * Complex.log (s / (c : ℂ)) + twist j = _
  rw [hdiv]
  dsimp only [kernelTwist]
  linear_combination -hcast

theorem differentiableOn_kernelLogDerivative [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (n : ℕ) :
    DifferentiableOn ℂ (kernelLogDerivative α₁ α₂ j n) (kernelDomain α₁ α₂ n) := by
  have hk := differentiableOn_kernel α₁ α₂ j n
  have hd := hk.deriv (isOpen_kernelDomain α₁ α₂ n)
  have hq := hd.div hk (fun x hx => kernel_ne_zero j n hx)
  apply hq.congr
  intro x hx
  rw [← logDeriv_kernel j n hx, logDeriv_apply, Pi.div_apply]

end ThisWork.Analytic
