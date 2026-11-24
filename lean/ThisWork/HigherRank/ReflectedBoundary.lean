module

public import ThisWork.HigherRank.ReferenceContour

/-! A regular reflected kernel near the negative-real boundary saddle.
All Gamma arguments have positive real part when `x.re < 0` and the upper
gaps are positive. This avoids taking a logarithm through Gamma poles. -/

@[expose] public section
namespace ThisWork.HigherRank

noncomputable def reflectedKernel (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (n : ℕ) (x : ℂ) : ℂ :=
  (Complex.Gamma (1 - x))⁻¹ ^ r *
    (∏ i, Complex.Gamma ((A i : ℂ) * n - x + 1)) *
    Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - x))

theorem boundaryKernel_eq_reflected {r : ℕ} (hr : 0 < r) (b : ℕ)
    (A : Fin (r - 1) → ℝ) (z : ℝ) (n : ℕ) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    boundaryKernel r b A z n x =
      ((Real.pi : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I * x) /
        Complex.sin ((Real.pi : ℂ) * x)) * reflectedKernel r b A z n x := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ : Complex.Gamma (1 - x) ≠ 0 := (mul_ne_zero_iff.mp
    (show Complex.Gamma x * Complex.Gamma (1 - x) ≠ 0 by
      rw [Complex.Gamma_mul_Gamma_one_sub]; exact div_ne_zero hπ hx)).2
  have hp : Complex.Gamma x * (Complex.Gamma (1 - x))⁻¹ ^ (r - 1) =
      ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * x)) *
        (Complex.Gamma (1 - x))⁻¹ ^ r := by
    calc
      _ = (Complex.Gamma x * Complex.Gamma (1 - x)) *
          (Complex.Gamma (1 - x))⁻¹ ^ r := by
        nth_rw 2 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne')]
        rw [pow_succ]
        field_simp
      _ = _ := by rw [Complex.Gamma_mul_Gamma_one_sub]
  unfold boundaryKernel reflectedKernel
  rw [hp]
  ring

theorem differentiableAt_reflectedKernel_of_re_lt_one {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℂ} (hx : x.re < 1) :
    DifferentiableAt ℂ (reflectedKernel r b A z n) x := by
  have h0 : 0 < (1 - x).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hd0 : DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma (1 - t)) x :=
    (Complex.hasDerivAt_Gamma_of_re_pos h0).differentiableAt.comp x (by fun_prop)
  have hi (i : Fin (r - 1)) :
      DifferentiableAt ℂ (fun t : ℂ => Complex.Gamma ((A i : ℂ) * n - t + 1)) x := by
    have hpos : 0 < ((A i : ℂ) * n - x + 1).re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re]
      nlinarith [hA i, Nat.cast_nonneg (α := ℝ) n]
    exact (Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt.comp x (by fun_prop)
  have hp := DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun i _ => hi i)
  have he : DifferentiableAt ℂ
      (fun t : ℂ => Complex.exp ((Real.log z : ℂ) * ((b : ℂ) * n - t))) x := by fun_prop
  exact (((hd0.inv (Complex.Gamma_ne_zero_of_re_pos h0)).pow r).fun_mul hp).fun_mul he

theorem differentiableAt_reflectedKernel {r : ℕ} {A : Fin (r - 1) → ℝ}
    (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (n : ℕ) {x : ℂ} (hx : x.re < 0) :
    DifferentiableAt ℂ (reflectedKernel r b A z n) x :=
  differentiableAt_reflectedKernel_of_re_lt_one hA b z n (hx.trans zero_lt_one)

end ThisWork.HigherRank
