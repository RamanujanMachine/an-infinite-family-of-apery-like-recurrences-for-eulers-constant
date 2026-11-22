module

public import ThisWork.HigherRank.Kernel

/-! Reflection of the boundary mode in arbitrary rank. All identities here
are for the actual Gamma factors; contour closure is a separate step. -/

@[expose] public section
namespace ThisWork.HigherRank

theorem gamma_mul_sin_div_pi {x : ℂ} (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    Complex.Gamma x * (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) =
      (Complex.Gamma (1 - x))⁻¹ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hprod : Complex.Gamma x * Complex.Gamma (1 - x) ≠ 0 := by
    rw [Complex.Gamma_mul_Gamma_one_sub]
    exact div_ne_zero hπ hx
  have hΓ := (mul_ne_zero_iff.mp hprod).2
  apply (mul_right_cancel₀ hΓ)
  rw [inv_mul_cancel₀ hΓ]
  calc
    _ = (Complex.Gamma x * Complex.Gamma (1 - x)) *
        Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ) := by ring
    _ = 1 := by rw [Complex.Gamma_mul_Gamma_one_sub]; field_simp

theorem gamma_power_reflection {r : ℕ} (hr : 0 < r) {x : ℂ}
    (hx : Complex.sin ((Real.pi : ℂ) * x) ≠ 0) :
    Complex.Gamma x ^ r * (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ (r - 1) =
      Complex.Gamma x * ((Complex.Gamma (1 - x))⁻¹) ^ (r - 1) := by
  calc
    _ = Complex.Gamma x *
        (Complex.Gamma x * (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ))) ^ (r - 1) := by
      nth_rw 1 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne')]
      rw [pow_succ, mul_pow]
      ring
    _ = _ := by rw [gamma_mul_sin_div_pi hx]

end ThisWork.HigherRank
