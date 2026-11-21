module
public import ThisWork.Trajectory.ReflectedCompactFamily
public import ThisWork.LocalKernelPhase
/-! The reflected saddle equation is the logarithmic derivative of the actual kernel. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

noncomputable def reflectedScaledKernel (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  reflectedKernel m d A₁ A₂ z n (-((sqrtScale n : ℂ) * s))

theorem reflectedScaledKernel_regular (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (s : ℂ)
    (hD : 0 < ((d : ℂ) * n - (sqrtScale n : ℂ) * s).re)
    (h₁ : 0 < ((A₁ : ℂ) * n + (sqrtScale n : ℂ) * s + 1).re)
    (h₂ : 0 < ((A₂ : ℂ) * n + (sqrtScale n : ℂ) * s + 1).re)
    (hB : 0 < (1 + (sqrtScale n : ℂ) * s).re) :
    DifferentiableAt ℂ (reflectedScaledKernel m d A₁ A₂ z n) s ∧
    reflectedScaledKernel m d A₁ A₂ z n s ≠ 0 ∧
    logDeriv (reflectedScaledKernel m d A₁ A₂ z n) s =
      (sqrtScale n : ℂ) * reflectedEquation d A₁ A₂ z n s := by
  let R : ℂ := (sqrtScale n : ℂ)
  let fD : ℂ → ℂ := fun t => Complex.Gamma ((d : ℂ) * n - R * t)
  let f₁ : ℂ → ℂ := fun t => Complex.Gamma ((A₁ : ℂ) * n + R * t + 1)
  let f₂ : ℂ → ℂ := fun t => Complex.Gamma ((A₂ : ℂ) * n + R * t + 1)
  let fB : ℂ → ℂ := fun t => Complex.Gamma (1 + R * t)
  let e : ℂ → ℂ := fun t => Complex.exp ((Real.log z : ℂ) * ((m : ℂ) * n + R * t))
  have aD : HasDerivAt (fun t => (d : ℂ) * n - R * t) (-R) s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul R).const_sub ((d : ℂ) * n)
  have a₁ (A : ℝ) : HasDerivAt (fun t => (A : ℂ) * n + R * t + 1) R s := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id s).const_mul R).const_add ((A : ℂ) * n)).add_const 1
  have aB : HasDerivAt (fun t => 1 + R * t) R s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul R).const_add 1
  have hne (w : ℂ) (hw : 0 < w.re) : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hdg (w : ℂ) (hw : 0 < w.re) : DifferentiableAt ℂ Complex.Gamma w :=
    Complex.differentiableAt_Gamma w (not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hw)))
  have dD : DifferentiableAt ℂ fD s := (hdg _ hD).comp s aD.differentiableAt
  have d₁ : DifferentiableAt ℂ f₁ s := (hdg _ h₁).comp s (a₁ A₁).differentiableAt
  have d₂ : DifferentiableAt ℂ f₂ s := (hdg _ h₂).comp s (a₁ A₂).differentiableAt
  have dB : DifferentiableAt ℂ fB s := (hdg _ hB).comp s aB.differentiableAt
  have de : HasDerivAt e (e s * ((Real.log z : ℂ) * R)) s := by
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id s).const_mul R).const_add ((m : ℂ) * n)).const_mul (Real.log z : ℂ)).cexp
  have nD : fD s ≠ 0 := hne _ hD
  have n₁ : f₁ s ≠ 0 := hne _ h₁
  have n₂ : f₂ s ≠ 0 := hne _ h₂
  have nB : fB s ≠ 0 := hne _ hB
  have ne : e s ≠ 0 := Complex.exp_ne_zero _
  have heq : reflectedScaledKernel m d A₁ A₂ z n =
      (fun t => fD t * f₁ t * f₂ t / fB t ^ 2 * e t) := by
    funext t
    simp only [reflectedScaledKernel, reflectedKernel, fD, f₁, f₂, fB, e, R,
      ← sub_eq_add_neg, sub_neg_eq_add]
  rw [heq]
  refine ⟨(((dD.mul d₁).mul d₂).div (dB.pow 2) (pow_ne_zero 2 nB)).mul de.differentiableAt,
    mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero nD n₁) n₂) (pow_ne_zero 2 nB)) ne, ?_⟩
  rw [logDeriv_fun_mul (f := fun t => fD t * f₁ t * f₂ t / fB t ^ 2) (g := e) s (div_ne_zero (mul_ne_zero (mul_ne_zero nD n₁) n₂) (pow_ne_zero 2 nB)) ne
    (((dD.mul d₁).mul d₂).div (dB.pow 2) (pow_ne_zero 2 nB)) de.differentiableAt,
    logDeriv_fun_div (f := fun t => fD t * f₁ t * f₂ t) (g := fun t => fB t ^ 2) s (mul_ne_zero (mul_ne_zero nD n₁) n₂) (pow_ne_zero 2 nB)
      ((dD.mul d₁).mul d₂) (dB.pow 2),
    logDeriv_fun_mul (f := fun t => fD t * f₁ t) (g := f₂) s (mul_ne_zero nD n₁) n₂ (dD.mul d₁) d₂,
    logDeriv_fun_mul (f := fD) (g := f₁) s nD n₁ dD d₁, logDeriv_fun_pow dB 2]
  have hlog (g : ℂ → ℂ) (v : ℂ) (hg : HasDerivAt g v s) (hpos : 0 < (g s).re) :=
    hg.logDeriv_Gamma (not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hpos)))
  have he : logDeriv e s = (Real.log z : ℂ) * R := by
    rw [logDeriv_apply, de.deriv, mul_div_cancel_left₀ _ ne]
  rw [hlog _ _ aD hD, hlog _ _ (a₁ A₁) h₁, hlog _ _ (a₁ A₂) h₂, hlog _ _ aB hB, he]
  dsimp only [reflectedEquation, R]
  norm_num only [Nat.cast_ofNat]
  ring

theorem eventually_reflectedScaledKernel_regular {d : ℕ} {A₁ A₂ z c : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hc : 0 < c) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ s ∈ ball (c : ℂ) (c / 4),
      DifferentiableAt ℂ (reflectedScaledKernel m d A₁ A₂ z n) s ∧
      reflectedScaledKernel m d A₁ A₂ z n s ≠ 0 ∧
      logDeriv (reflectedScaledKernel m d A₁ A₂ z n) s =
        (sqrtScale n : ℂ) * reflectedEquation d A₁ A₂ z n s := by
  filter_upwards [eventually_right_factor_conditions (Nat.cast_pos.mpr hd) (5 * c / 4),
    eventually_gt_atTop (0 : ℕ)] with n hD hn
  refine ⟨hn, fun s hs => ?_⟩
  have hsD : s ∈ saddleDisk c .three := by
    simpa only [saddleDisk, rho_three, mul_one] using ball_subset_closedBall hs
  have hre : 0 < s.re := by
    have h := saddleDisk_region hc .three hsD
    change c / 2 ≤ s.re at h
    linarith
  have hR := sqrtScale_pos hn
  have hbound := mul_le_mul_of_nonneg_left ((Complex.re_le_norm s).trans (saddleDisk_norm_le hc .three hsD)) hR.le
  apply reflectedScaledKernel_regular
  · simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    nlinarith [hD.1, hD.2]
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.one_re, zero_mul, mul_zero, sub_zero]
    positivity
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im, Complex.one_re, zero_mul, mul_zero, sub_zero]
    positivity
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, zero_mul, sub_zero]
    positivity

end ThisWork.Trajectory
