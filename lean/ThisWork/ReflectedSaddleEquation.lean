module

public import ThisWork.ReflectedBoundary
public import ThisWork.Scales
public import ThisWork.DigammaBound

/-! The exact logarithmic derivative of the regular reflected kernel at the
negative-real saddle. All Gamma arguments lie in the right half-plane. -/

@[expose] public section
namespace ThisWork

theorem upper_re_pos_of_re_lt_one {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (n : ℕ) {x : ℂ} (hx : x.re < 1) (i : Fin (r - 1)) :
    0 < ((A i : ℂ) * n - x + 1).re := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re]
  nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n]

theorem upper_re_pos_of_re_nonpos {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (n : ℕ) {x : ℂ} (hx : x.re ≤ 0) (i : Fin (r - 1)) :
    0 < ((A i : ℂ) * n - x + 1).re :=
  upper_re_pos_of_re_lt_one hA n (hx.trans_lt zero_lt_one) i

theorem logDeriv_reflected_lower_of_re_lt_one {r : ℕ} {x : ℂ} (hx : x.re < 1) :
    logDeriv (fun t : ℂ => (Complex.Gamma (1 - t))⁻¹ ^ r) x =
      (r : ℂ) * Complex.digamma (1 - x) := by
  have hpos : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hd : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (1 - t)) x :=
    (Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt.comp x (by fun_prop)
  have ha : HasDerivAt (fun t : ℂ => 1 - t) (-1) x := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using (hasDerivAt_const x (1 : ℂ)).sub (hasDerivAt_id x)
  have he : logDeriv (fun t : ℂ => Complex.Gamma (1 - t)) x = -Complex.digamma (1 - x) := by
    simpa only [neg_one_mul] using ha.logDeriv_Gamma
      (Analytic.not_neg_nat_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hpos)))
  have hfun : (fun t : ℂ => (Complex.Gamma (1 - t))⁻¹ ^ r) =
      (fun t : ℂ => Complex.Gamma (1 - t) ^ (-(r : ℤ))) := by
    funext t
    simp
  rw [hfun, logDeriv_fun_zpow hd, he]
  push_cast
  ring

theorem logDeriv_reflected_lower {r : ℕ} {x : ℂ} (hx : x.re < 0) :
    logDeriv (fun t : ℂ => (Complex.Gamma (1 - t))⁻¹ ^ r) x =
      (r : ℂ) * Complex.digamma (1 - x) :=
  logDeriv_reflected_lower_of_re_lt_one (hx.trans zero_lt_one)

theorem logDeriv_reflectedKernel_of_re_lt_one {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℂ} (hx : x.re < 1) :
    logDeriv (reflectedKernel r b A z n) x =
      (r : ℂ) * Complex.digamma (1 - x) -
        (∑ i, Complex.digamma ((A i : ℂ) * n - x + 1)) - (Real.log z : ℂ) := by
  let l : ℂ → ℂ := fun t => (Complex.Gamma (1 - t))⁻¹ ^ r
  let g : ℂ → ℂ := fun t => ∏ i, Complex.Gamma ((A i : ℂ) * n - t + 1)
  let e : ℂ → ℂ := fun t => (Real.log z : ℂ) * ((b : ℂ) * n - t)
  have hpos : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hl : l x ≠ 0 := pow_ne_zero r (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hpos))
  have hdl : DifferentiableAt ℂ l x :=
    (((Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt.comp x
      (show DifferentiableAt ℂ (fun t : ℂ => 1 - t) x by fun_prop)).inv
        (Complex.Gamma_ne_zero_of_re_pos hpos)).pow r
  have hu := upper_re_pos_of_re_lt_one hA n hx
  have hg : g x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => Complex.Gamma_ne_zero_of_re_pos (hu i))
  have hdg : DifferentiableAt ℂ g x := DifferentiableAt.fun_finsetProd
    (fun i _ => (Complex.hasDerivAt_Gamma_of_re_pos (hu i)).differentiableAt.comp x
      (show DifferentiableAt ℂ (fun t : ℂ => (A i : ℂ) * n - t + 1) x by fun_prop))
  have hde : HasDerivAt e (-(Real.log z : ℂ)) x := by
    convert (((hasDerivAt_const x ((b : ℂ) * n)).sub (hasDerivAt_id x)).const_mul (Real.log z : ℂ)) using 1
    · rfl
    · ring
  have he : logDeriv (fun t => Complex.exp (e t)) x = -(Real.log z : ℂ) := by
    rw [logDeriv_apply, hde.cexp.deriv]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  change logDeriv (fun t => l t * g t * Complex.exp (e t)) x = _
  rw [logDeriv_fun_mul (f := fun t => l t * g t) (g := fun t => Complex.exp (e t)) x
    (mul_ne_zero hl hg) (Complex.exp_ne_zero _) (hdl.fun_mul hdg) hde.cexp.differentiableAt,
    logDeriv_fun_mul (f := l) (g := g) x hl hg hdl hdg,
    logDeriv_reflected_lower_of_re_lt_one hx, logDeriv_upperProduct_of_re_pos hu, he]
  ring

theorem logDeriv_reflectedKernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℂ} (hx : x.re < 0) :
    logDeriv (reflectedKernel r b A z n) x =
      (r : ℂ) * Complex.digamma (1 - x) -
        (∑ i, Complex.digamma ((A i : ℂ) * n - x + 1)) - (Real.log z : ℂ) :=
  logDeriv_reflectedKernel_of_re_lt_one hA b z n (hx.trans zero_lt_one)

theorem reflectedKernel_ne_zero_of_re_lt_one {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℂ} (hx : x.re < 1) :
    reflectedKernel r b A z n x ≠ 0 := by
  have hpos : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  exact mul_ne_zero (mul_ne_zero
    (pow_ne_zero r (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hpos)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ =>
      Complex.Gamma_ne_zero_of_re_pos (upper_re_pos_of_re_lt_one hA n hx i)))) (Complex.exp_ne_zero _)

/-- The reflected lower Gamma factor has a uniform error without approaching
the poles on the negative real axis. -/
theorem norm_digamma_add_one_sub_log_le {w : ℂ} (hw : 0 < w.re) :
    ‖Complex.digamma (w + 1) - Complex.log w‖ ≤ 2 / w.re := by
  have hp : 1 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hd := Analytic.norm_digamma_sub_log_le hp
  simp only [Complex.add_re, Complex.one_re, add_sub_cancel_right] at hd
  calc
    _ ≤ ‖Complex.digamma (w + 1) - Complex.log (w + 1)‖ +
        ‖Complex.log (w + 1) - Complex.log w‖ := by
          calc
            _ = ‖(Complex.digamma (w + 1) - Complex.log (w + 1)) +
                (Complex.log (w + 1) - Complex.log w)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
    _ ≤ 1 / w.re + 1 / w.re := add_le_add hd (Analytic.norm_log_add_one_sub_le hw)
    _ = _ := by ring

end ThisWork
