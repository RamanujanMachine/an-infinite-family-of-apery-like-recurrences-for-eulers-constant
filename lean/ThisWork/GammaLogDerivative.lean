module

public import ThisWork.Argument
public import ThisWork.GammaApproximation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Passing Euler's approximants to the logarithmic derivative of Gamma. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory Asymptotics
open scoped Topology

theorem shifted_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (k : ℕ) : s + k ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at he
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem differentiableOn_GammaSeq {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun s => Complex.GammaSeq s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hp : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ)) s :=
    (differentiableAt_id.const_cpow (Or.inl hn0)).mul_const _
  have hd : DifferentiableAt ℂ (fun z : ℂ => ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) s := by fun_prop
  have hden : (∏ k ∈ Finset.range (n + 1), (s + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => shifted_ne_zero_of_re_pos hs k)
  change DifferentiableWithinAt ℂ (fun z => (n : ℂ) ^ z * (Nat.factorial n : ℂ) /
    ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) {z : ℂ | 0 < z.re} s
  simpa only [Pi.div_def] using (hp.div hd hden).differentiableWithinAt

theorem GammaSeq_logDeriv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => logDeriv (fun z => Complex.GammaSeq z (n + 1)) s)
      atTop (𝓝 (Complex.digamma s)) := by
  exact Complex.logDeriv_tendsto (isOpen_lt continuous_const Complex.continuous_re) hs
    GammaSeq_tendsto_locally_uniform (Eventually.of_forall (fun n => differentiableOn_GammaSeq (Nat.succ_ne_zero n)))
    (Complex.Gamma_ne_zero_of_re_pos hs)

theorem logDeriv_GammaSeq {n : ℕ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun z => Complex.GammaSeq z n) s =
      Complex.log (n : ℂ) - ∑ k ∈ Finset.range (n + 1), (s + (k : ℂ))⁻¹ := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hpow := (Complex.hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := s) (Or.inl hn0)).hasDerivAt
  have hpnz : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
  have hd : DifferentiableAt ℂ (fun z : ℂ => ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) s := by fun_prop
  have hden : (∏ k ∈ Finset.range (n + 1), (s + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => shifted_ne_zero_of_re_pos hs k)
  have hpLog : logDeriv (fun z : ℂ => (n : ℂ) ^ z) s = Complex.log (n : ℂ) := by
    rw [logDeriv_apply, hpow.deriv]
    exact mul_div_cancel_left₀ _ hpnz
  have hdLog : logDeriv (fun z : ℂ => ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) s =
      ∑ k ∈ Finset.range (n + 1), (s + (k : ℂ))⁻¹ := by
    rw [logDeriv_fun_prod (fun k _ => shifted_ne_zero_of_re_pos hs k) (fun k _ => by fun_prop)]
    apply Finset.sum_congr rfl
    intro k hk
    simp [logDeriv_apply]
  change logDeriv (fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ) /
    ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) s = _
  rw [logDeriv_fun_div (f := fun z : ℂ => (n : ℂ) ^ z * (Nat.factorial n : ℂ))
    (g := fun z : ℂ => ∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) s (mul_ne_zero hpnz hfac) hden (hpow.mul_const _).differentiableAt hd,
    logDeriv_mul_const s _ hfac, hpLog, hdLog]

/-- Gauss' finite-sum limit for digamma on the right half-plane, derived from
locally uniform convergence rather than differentiation of a pointwise limit. -/
theorem digamma_eq_gauss_limit {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => Complex.log ((n + 1 : ℕ) : ℂ) -
      ∑ k ∈ Finset.range (n + 2), (s + (k : ℂ))⁻¹) atTop (𝓝 (Complex.digamma s)) := by
  simpa only [logDeriv_GammaSeq (Nat.succ_ne_zero _) hs, Nat.add_assoc] using GammaSeq_logDeriv_tendsto hs

end ThisWork.Analytic
