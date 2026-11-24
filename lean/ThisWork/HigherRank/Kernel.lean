module

public import ThisWork.HigherRank.Definitions
public import ThisWork.PoleFree
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! Pole separation and analyticity of the actual arbitrary-rank kernels. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set

def kernelDomain (r : ℕ) (A : Fin (r - 1) → ℝ) (n : ℕ) : Set ℂ :=
  {x | x ∈ Complex.slitPlane ∧ ∀ i, x.re < A i * n + 1}

theorem isOpen_kernelDomain (r : ℕ) (A : Fin (r - 1) → ℝ) (n : ℕ) :
    IsOpen (kernelDomain r A n) := by
  have h : IsOpen (Complex.slitPlane ∩ ⋂ i, {x : ℂ | x.re < A i * n + 1}) :=
    Complex.isOpen_slitPlane.inter (isOpen_iInter_of_finite
      (fun i => isOpen_lt Complex.continuous_re continuous_const))
  convert h using 1
  ext x
  simp [kernelDomain]

theorem upper_re_pos {r : ℕ} {A : Fin (r - 1) → ℝ} {n : ℕ} {x : ℂ}
    (hx : x ∈ kernelDomain r A n) (i : Fin (r - 1)) :
    0 < ((A i : ℂ) * n - x + 1).re := by
  have hi := hx.2 i
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re]
  linarith

theorem kernel_ne_zero {r : ℕ} {A : Fin (r - 1) → ℝ}
    (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) {x : ℂ} (hx : x ∈ kernelDomain r A n) :
    kernel r b A z j n x ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero r (Complex.Gamma_ne_zero
          (Analytic.not_neg_nat_of_mem_slitPlane hx.1))
      · exact Finset.prod_ne_zero_iff.mpr
          (fun i _ => Complex.Gamma_ne_zero_of_re_pos (upper_re_pos hx i))
    · exact Complex.exp_ne_zero _
  · exact Complex.exp_ne_zero _

theorem differentiableAt_kernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) {x : ℂ} (hx : x ∈ kernelDomain r A n) :
    DifferentiableAt ℂ (kernel r b A z j n) x := by
  have hg := Complex.differentiableAt_Gamma x
    (Analytic.not_neg_nat_of_mem_slitPlane hx.1)
  have hi (i : Fin (r - 1)) :
      DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma ((A i : ℂ) * n - t + 1)) x :=
    (Complex.hasDerivAt_Gamma_of_re_pos (upper_re_pos hx i)).differentiableAt.comp x (by fun_prop)
  have hp := DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun i _ => hi i)
  have he : DifferentiableAt ℂ
      (fun t : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * j * t)) x := by fun_prop
  have hz : DifferentiableAt ℂ
      (fun t : ℂ => Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - t))) x := by fun_prop
  exact (((hg.pow r).fun_mul hp).fun_mul he).fun_mul hz

theorem referenceContour_mem_kernelDomain {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (n : ℕ) {x : ℂ}
    (hx : x ∈ Analytic.hankelTrace (1 / 2) 1) : x ∈ kernelDomain r A n := by
  refine ⟨Analytic.hankelTrace_mem_slitPlane (by norm_num) (by norm_num) hx, ?_⟩
  intro i
  have hr := Analytic.hankelTrace_re_le hx
  have hi := hA i
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem logDeriv_upperProduct_of_re_pos {r : ℕ} {A : Fin (r - 1) → ℝ} {n : ℕ} {x : ℂ}
    (hx : ∀ i, 0 < ((A i : ℂ) * n - x + 1).re) :
    logDeriv (fun t : ℂ => ∏ i, Complex.Gamma ((A i : ℂ) * n - t + 1)) x =
      -∑ i, Complex.digamma ((A i : ℂ) * n - x + 1) := by
  have ha (i : Fin (r - 1)) :
      HasDerivAt (fun t : ℂ => (A i : ℂ) * n - t + 1) (-1) x := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using
      ((hasDerivAt_const x ((A i : ℂ) * n)).sub (hasDerivAt_id x)).add_const 1
  have hd (i : Fin (r - 1)) :
      DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma ((A i : ℂ) * n - t + 1)) x :=
    (Complex.hasDerivAt_Gamma_of_re_pos (hx i)).differentiableAt.comp x
      (ha i).differentiableAt
  rw [logDeriv_fun_prod (f := fun i => fun t : ℂ => Complex.Gamma ((A i : ℂ) * n - t + 1))
    (fun i _ => Complex.Gamma_ne_zero_of_re_pos (hx i))
    (fun i _ => hd i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [neg_one_mul] using (ha i).logDeriv_Gamma
    (Analytic.not_neg_nat_of_mem_slitPlane
      (Complex.mem_slitPlane_iff.mpr (Or.inl (hx i))))

theorem logDeriv_upperProduct {r : ℕ} {A : Fin (r - 1) → ℝ} {n : ℕ} {x : ℂ}
    (hx : x ∈ kernelDomain r A n) :
    logDeriv (fun t : ℂ => ∏ i, Complex.Gamma ((A i : ℂ) * n - t + 1)) x =
      -∑ i, Complex.digamma ((A i : ℂ) * n - x + 1) :=
  logDeriv_upperProduct_of_re_pos (upper_re_pos hx)

theorem logDeriv_kernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (b : ℕ) (z : ℝ) (j : ℤ) (n : ℕ) {x : ℂ} (hx : x ∈ kernelDomain r A n) :
    logDeriv (kernel r b A z j n) x =
      (r : ℂ) * Complex.digamma x - (∑ i, Complex.digamma ((A i : ℂ) * n - x + 1)) +
        2 * (Real.pi : ℂ) * Complex.I * j - (Real.log z : ℂ) := by
  let τ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * j
  let g : ℂ → ℂ := fun t => ∏ i, Complex.Gamma ((A i : ℂ) * n - t + 1)
  let e : ℂ → ℂ := fun t => τ * t + (Real.log z : ℂ) * ((b : ℂ) * n - t)
  have hdΓ := Complex.differentiableAt_Gamma x (Analytic.not_neg_nat_of_mem_slitPlane hx.1)
  have hnΓ := pow_ne_zero r (Complex.Gamma_ne_zero (Analytic.not_neg_nat_of_mem_slitPlane hx.1))
  have hng : g x ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => Complex.Gamma_ne_zero_of_re_pos (upper_re_pos hx i))
  have hdg : DifferentiableAt ℂ g x := DifferentiableAt.fun_finsetProd
    (fun i _ => (Complex.hasDerivAt_Gamma_of_re_pos (upper_re_pos hx i)).differentiableAt.comp x
      (show DifferentiableAt ℂ (fun t : ℂ => (A i : ℂ) * n - t + 1) x by fun_prop))
  have hde : HasDerivAt e (τ - (Real.log z : ℂ)) x := by
    convert ((hasDerivAt_id x).const_mul τ).add
      (((hasDerivAt_const x ((b : ℂ) * n)).sub (hasDerivAt_id x)).const_mul (Real.log z : ℂ)) using 1
    · rfl
    · ring
  have hfun : kernel r b A z j n =
      (fun t => Complex.Gamma t ^ r * g t * Complex.exp (e t)) := by
    funext t
    simp only [kernel, e, Complex.exp_add, τ, g]
    ring
  rw [hfun, logDeriv_fun_mul (f := fun t => Complex.Gamma t ^ r * g t)
      (g := fun t => Complex.exp (e t)) x (mul_ne_zero hnΓ hng)
      (Complex.exp_ne_zero _) ((hdΓ.pow r).fun_mul hdg) hde.cexp.differentiableAt,
    logDeriv_fun_mul (f := fun t => Complex.Gamma t ^ r) (g := g) x hnΓ hng (hdΓ.pow r) hdg]
  have hΓ : logDeriv (fun t => Complex.Gamma t ^ r) x = (r : ℂ) * Complex.digamma x := by
    simpa only [Complex.digamma_def] using logDeriv_fun_pow hdΓ r
  have he : logDeriv (fun t => Complex.exp (e t)) x = τ - (Real.log z : ℂ) := by
    rw [logDeriv_apply, hde.cexp.deriv]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  rw [hΓ, logDeriv_upperProduct hx, he]
  dsimp only [τ]
  ring

end ThisWork.HigherRank
