module

public import Neuschel.PhaseFactor
public import Mathlib.Analysis.Analytic.OfScalars

/-! Bridge from the convergent scalar expansions in Neuschel's hypotheses. -/

public section

namespace Neuschel

open Set Filter
open scoped Topology

def shiftedCoefficients (μ : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if μ ≤ n then b (n - μ) else 0

@[simp] theorem shiftedCoefficients_add (μ n : ℕ) (b : ℕ → ℂ) :
    shiftedCoefficients μ b (n + μ) = b n := by
  simp [shiftedCoefficients]

@[simp] theorem shiftedCoefficients_self (μ : ℕ) (b : ℕ → ℂ) :
    shiftedCoefficients μ b μ = b 0 := by
  simp [shiftedCoefficients]

theorem shiftedCoefficients_of_lt {μ n : ℕ} (b : ℕ → ℂ) (hn : n < μ) :
    shiftedCoefficients μ b n = 0 :=
  ite_eq_right (Nat.not_le_of_gt hn)

theorem hasSum_shiftedCoefficients {μ : ℕ} {b : ℕ → ℂ} {x y : ℂ}
    (hs : HasSum (fun n => b n * x ^ (μ + n)) y) :
    HasSum (fun n => x ^ n * shiftedCoefficients μ b n) y := by
  apply (hasSum_nat_add_iff' μ).mp
  have hzero : ∑ i ∈ Finset.range μ, x ^ i * shiftedCoefficients μ b i = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      rw [shiftedCoefficients_of_lt b (Finset.mem_range.mp hi), mul_zero])
  rw [hzero, sub_zero]
  simpa [shiftedCoefficients, Nat.add_comm, mul_comm] using hs

theorem hasFPowerSeriesAt_of_shifted_expansion {μ : ℕ} {a : ℂ} {b : ℕ → ℂ} {f : ℂ → ℂ}
    (hs : ∀ᶠ t in 𝓝 a, HasSum (fun n => b n * (t - a) ^ (μ + n)) (f t)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (shiftedCoefficients μ b)) a :=
  hasFPowerSeriesAt_iff'.mpr (hs.mono (fun t ht => by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] using
      hasSum_shiftedCoefficients ht))

theorem phaseQuotient_center_of_expansion {Z : Type*} (k : ℕ) {a : ℂ}
    {q : ℂ → Z → ℂ} {c : ℕ → Z → ℂ} {z : Z}
    (hs : ∀ᶠ t in 𝓝 a, HasSum (fun n => c n z * (t - a) ^ (k + n)) (q t z)) :
    phaseQuotient k a q a z = c 0 z := by
  simpa only [FormalMultilinearSeries.coeff_ofScalars, shiftedCoefficients_self] using
    phaseQuotient_center_eq_coeff k (hasFPowerSeriesAt_of_shifted_expansion hs)

theorem eq_pow_mul_phaseQuotient_of_expansion {Z : Type*} (k : ℕ) {a : ℂ}
    {q : ℂ → Z → ℂ} {c : ℕ → Z → ℂ} {z : Z}
    (hs : ∀ᶠ t in 𝓝 a, HasSum (fun n => c n z * (t - a) ^ (k + n)) (q t z)) (t : ℂ) :
    q t z = (t - a) ^ k * phaseQuotient k a q t z :=
  eq_pow_mul_phaseQuotient k (hasFPowerSeriesAt_of_shifted_expansion hs)
    (fun n hn => by simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      shiftedCoefficients_of_lt (fun n => c n z) hn) t

/-- The amplitude expansion has the same analytic factorization as the centered
phase expansion, with any nonnegative order of vanishing. -/
theorem exists_analytic_factor_from_expansion {Z : Type*} [TopologicalSpace Z]
    (k : ℕ) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {q : ℂ → Z → ℂ} (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {c : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun n => c n z * (t - a) ^ (k + n)) (q t z))
    (hc0 : ∀ z, c 0 z ≠ 0) :
    ∃ g : ℂ → Z → ℂ, ContinuousOn (Function.uncurry g) (G ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun t => g t z) G) ∧ (∀ z, g a z = 1) ∧
      ∀ t ∈ G, ∀ z, q t z = c 0 z * (t - a) ^ k * g t z := by
  simpa only [FormalMultilinearSeries.coeff_ofScalars, shiftedCoefficients_self] using
    exists_normalized_analytic_factor k hG ha hq hd
      (fun z => hasFPowerSeriesAt_of_shifted_expansion (hs z))
      (fun z n hn => by simpa only [FormalMultilinearSeries.coeff_ofScalars] using
        shiftedCoefficients_of_lt (fun n => c n z) hn)
      (fun z => by simpa only [FormalMultilinearSeries.coeff_ofScalars,
        shiftedCoefficients_self] using hc0 z)

/-- Neuschel's convergent phase expansion supplies all regularity of the
normalized factor, even when each parameter has its own convergence neighborhood. -/
theorem exists_phase_factor_from_expansion {Z : Type*} [TopologicalSpace Z]
    (μ : ℕ) {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {p : ℂ → Z → ℂ} (hp : ContinuousOn (Function.uncurry p) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) G) {b : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun n => b n z * (t - a) ^ (μ + n)) (p t z - p a z))
    (hb0 : ∀ z, b 0 z ≠ 0) :
    Continuous (b 0) ∧
    ∃ h : ℂ → Z → ℂ, ContinuousOn (Function.uncurry h) (G ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun t => h t z) G) ∧ (∀ z, h a z = 1) ∧
      ∀ t ∈ G, ∀ z, p t z - p a z = b 0 z * (t - a) ^ μ * h t z := by
  have hs' := fun z => hasFPowerSeriesAt_of_shifted_expansion (hs z)
  simpa only [FormalMultilinearSeries.coeff_ofScalars, shiftedCoefficients_self] using
    exists_normalized_phase_factor μ hG ha hp hd hs'
      (fun z n hn => by simpa only [FormalMultilinearSeries.coeff_ofScalars] using
        shiftedCoefficients_of_lt (fun n => b n z) hn)
      (fun z => by simpa only [FormalMultilinearSeries.coeff_ofScalars,
        shiftedCoefficients_self] using hb0 z)

end Neuschel
