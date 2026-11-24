module

public import ThisWork.HigherRank.LocalWindowIdentity
public import ThisWork.HigherRank.ParabolicContour

/-! The curved local Laplace integrals are exactly the corresponding
windows of the global translated parabola, including their Jacobians. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter Metric MeasureTheory
open scoped Topology

theorem quadratic_half_integral_eq_parabolic (a auxB d cutoff : ℝ) (σ : ℂ) (f : ℂ → ℂ) :
    (∫ u in (0 : ℝ)..cutoff,
      ((d : ℂ) * (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I) - 2 * ((u : ℂ) * (d : ℂ)))) *
        f (quadraticArc (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) ((u : ℂ) * (d : ℂ)) + σ)) =
      ∫ t in auxB..(auxB + d * cutoff), (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
        f (σ - parabolicPoint a auxB + parabolicPoint a t) := by
  let g : ℝ → ℂ := fun t => (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
    f (σ - parabolicPoint a auxB + parabolicPoint a t)
  have hs := intervalIntegral.smul_integral_comp_add_mul g d auxB (a := 0) (b := cutoff)
  simp only [mul_zero, add_zero] at hs
  change _ = ∫ t in auxB..(auxB + d * cutoff), g t
  rw [← hs, Complex.real_smul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  have hcurve : quadraticArc (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I))
      ((u : ℂ) * (d : ℂ)) + σ = σ - parabolicPoint a auxB + parabolicPoint a (auxB + d * u) := by
    rw [show (u : ℂ) * (d : ℂ) = ((d * u : ℝ) : ℂ) by push_cast; ring,
      quadraticArc_parabolicPoint]
    ring
  have htangent : 2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I) - 2 * ((u : ℂ) * (d : ℂ)) =
      2 * Complex.I * ((a : ℂ) + ((auxB + d * u : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  dsimp only [g]
  rw [hcurve, htangent]
  ring

theorem two_sided_quadratic_integral_eq_parabolic_window
    (a auxB speed cplus cminus : ℝ) (σ : ℂ) (f : ℂ → ℂ)
    (hm : IntervalIntegrable (fun t : ℝ => (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
      f (σ - parabolicPoint a auxB + parabolicPoint a t)) volume (auxB - speed * cminus) auxB)
    (hp : IntervalIntegrable (fun t : ℝ => (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
      f (σ - parabolicPoint a auxB + parabolicPoint a t)) volume auxB (auxB + speed * cplus)) :
    (∫ u in (0 : ℝ)..cplus,
      ((speed : ℂ) * (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I) - 2 * ((u : ℂ) * (speed : ℂ)))) *
        f (quadraticArc (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) ((u : ℂ) * (speed : ℂ)) + σ)) -
    (∫ u in (0 : ℝ)..cminus,
      ((-speed : ℂ) * (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I) - 2 * ((u : ℂ) * (-speed : ℂ)))) *
        f (quadraticArc (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) ((u : ℂ) * (-speed : ℂ)) + σ)) =
    ∫ t in (auxB - speed * cminus)..(auxB + speed * cplus),
      (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) * f (σ - parabolicPoint a auxB + parabolicPoint a t) := by
  have hplus := quadratic_half_integral_eq_parabolic a auxB speed cplus σ f
  have hminus := quadratic_half_integral_eq_parabolic a auxB (-speed) cminus σ f
  simp only [Complex.ofReal_neg] at hminus
  rw [show auxB + -speed * cminus = auxB - speed * cminus by ring] at hminus
  rw [intervalIntegral.integral_symm (auxB - speed * cminus) auxB] at hminus
  linear_combination hplus - hminus + intervalIntegral.integral_add_adjacent_intervals hm hp

theorem eventually_intervalIntegrable_parabolic_power {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (b : ℕ) (z : ℝ) (j : ℤ)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ ≤ a ^ 2 / 8 → ∀ k : ℕ, ∀ u v : ℝ,
      IntervalIntegrable (fun t : ℝ => (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
        ((δ + parabolicPoint a t) ^ k *
          kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a t)))) volume u v := by
  filter_upwards [eventually_translated_parabola_in_kernelDomain hr hA ha] with n hn δ hδ k u v
  have hc : Continuous (fun t : ℝ => kernel r b A z j n
      ((largeScale r n : ℂ) * (δ + parabolicPoint a t))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_kernel b z j n (hn δ hδ t)).continuousAt.comp
      (f := fun t : ℝ => (largeScale r n : ℂ) * (δ + parabolicPoint a t))
      (by unfold parabolicPoint; fun_prop)
  apply Continuous.intervalIntegrable
  exact (by fun_prop : Continuous (fun t : ℝ => 2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I))).mul
    ((by unfold parabolicPoint; fun_prop : Continuous (fun t : ℝ => (δ + parabolicPoint a t) ^ k)).mul hc)

namespace CompactSaddleFamily.LocalParabolicData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {a auxB radius : ℝ}
    {S : CompactSaddleFamily r A z j (parabolicPoint a auxB) radius}
    (D : S.LocalParabolicData (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)))

theorem eventually_localKernelMoment_eq_parabolic_window (hr : 0 < r)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (b : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : ℂ, ‖σ - parabolicPoint a auxB‖ ≤ a ^ 2 / 8 → ∀ k : ℕ,
      D.localKernelMoment b n σ k =
        ∫ t in (auxB - D.speed * D.negative.cutoff)..(auxB + D.speed * D.positive.cutoff),
          (2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I)) *
            ((σ - parabolicPoint a auxB + parabolicPoint a t) ^ k *
              kernel r b A z j n ((largeScale r n : ℂ) *
                (σ - parabolicPoint a auxB + parabolicPoint a t))) := by
  filter_upwards [eventually_intervalIntegrable_parabolic_power hr hA b z j ha] with n hn σ hσ k
  simpa only [localKernelMoment, kernelHalfMoment, Complex.ofReal_neg] using
    two_sided_quadratic_integral_eq_parabolic_window a auxB D.speed D.positive.cutoff D.negative.cutoff σ
    (fun s => s ^ k * kernel r b A z j n ((largeScale r n : ℂ) * s))
    (hn _ hσ k _ _) (hn _ hσ k _ _)

end CompactSaddleFamily.LocalParabolicData

end ThisWork.HigherRank
