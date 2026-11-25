module

public import ThisWork.Reflection
public import Mathlib.Data.Nat.Choose.Sum

/-! Exact finite Fourier identities for the even-rank boundary mode. -/

@[expose] public section
namespace ThisWork

theorem exp_mul_binomial (p : ℕ) (a u : ℂ) :
    Complex.exp (a * u) * (1 - Complex.exp (-u)) ^ p =
      ∑ k ∈ Finset.range (p + 1),
        ((-1 : ℂ) ^ k * (p.choose k : ℂ)) * Complex.exp ((a - k) * u) := by
  rw [show 1 - Complex.exp (-u) = -Complex.exp (-u) + 1 by ring, add_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_pow, mul_one]
  calc
    _ = ((-1 : ℂ) ^ k * (p.choose k : ℂ)) *
        (Complex.exp (a * u) * Complex.exp (-u) ^ k) := by
      rw [neg_eq_neg_one_mul, mul_pow]
      ring
    _ = _ := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      ring

theorem sine_exp_factor (x : ℂ) :
    Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
        (1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * x))) /
          (2 * (Real.pi : ℂ) * Complex.I) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * x)) =
        Complex.exp (-((Real.pi : ℂ) * x) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_sub, mul_one, he, Complex.sin]
  rw [show ((Real.pi : ℂ) * x) * Complex.I = (Real.pi : ℂ) * Complex.I * x by ring]
  field_simp
  simp only [Complex.I_sq]
  ring

theorem even_boundary_fourier (p h : ℕ) (hp : p + 1 = 2 * h) (x : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I) ^ p *
      Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
        (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ p =
      ∑ k ∈ Finset.range (p + 1), ((-1 : ℂ) ^ k * (p.choose k : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((h : ℤ) - k) * x) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I * x) ^ (p + 1) =
      Complex.exp ((h : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * x)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [show ((p + 1 : ℕ) : ℂ) = 2 * (h : ℂ) by exact_mod_cast hp]
    ring
  have hbase : (2 * (Real.pi : ℂ) * Complex.I) ^ p *
      Complex.exp ((Real.pi : ℂ) * Complex.I * x) *
        (Complex.sin ((Real.pi : ℂ) * x) / (Real.pi : ℂ)) ^ p =
      Complex.exp ((h : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * x)) *
        (1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * x))) ^ p := by
    rw [← hE, sine_exp_factor, div_pow, mul_pow, pow_succ]
    field_simp
    exact mul_pow _ _ _
  rw [hbase, exp_mul_binomial]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  push_cast
  ring

end ThisWork
