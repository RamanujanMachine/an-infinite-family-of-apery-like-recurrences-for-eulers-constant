module

public import ThisWork.NormalizedLocalMoments

/-! Exact identification of the parabolic local Laplace moments with the
actual Gamma-kernel contour windows. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric
open scoped Topology OnePoint

theorem quadraticArc_parabolicPoint (a auxB t : ℝ) :
    quadraticArc (2 * Complex.I * ((a : ℂ) + (auxB : ℂ) * Complex.I)) t =
      parabolicPoint a (auxB + t) - parabolicPoint a auxB := by
  unfold quadraticArc parabolicPoint
  push_cast
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

namespace CompactSaddleFamily.LocalParabolicData

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}
    {S : CompactSaddleFamily r A z j ζ δ} {v : ℂ} (D : S.LocalParabolicData v)

noncomputable def kernelHalfMoment (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ) (v : ℂ)
    (b n : ℕ) (σ : ℂ) (k : ℕ) (d cutoff : ℝ) : ℂ :=
  ∫ u in 0..cutoff, ((d : ℂ) * (v - 2 * ((u : ℂ) * (d : ℂ)))) *
    ((quadraticArc v ((u : ℂ) * (d : ℂ)) + σ) ^ k *
      kernel r b A z j n ((largeScale r n : ℂ) * (quadraticArc v ((u : ℂ) * (d : ℂ)) + σ)))

noncomputable def localKernelMoment (b n : ℕ) (σ : ℂ) (k : ℕ) : ℂ :=
  kernelHalfMoment A z j v b n σ k D.speed D.positive.cutoff -
    kernelHalfMoment A z j v b n σ k (-D.speed) D.negative.cutoff

theorem eventually_localKernelMoment_eq_phase (hr : 0 < r) (hA : ∀ i, 0 < A i)
    (hslit : ball ζ δ ⊆ Complex.slitPlane) (b k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      D.localKernelMoment b (n + D.shift + S.firstIndex) (S.saddle (n + D.shift)) k =
        kernel r b A z j (n + D.shift + S.firstIndex)
          ((largeScale r (n + D.shift + S.firstIndex) : ℂ) * S.saddle (n + D.shift)) *
            D.localMoment (largeScale r (n + D.shift + S.firstIndex)) k n := by
  filter_upwards [(tendsto_add_atTop_nat D.shift).eventually
    (S.eventually_kernel_eq_phase hr hA hslit b)] with n hn
  have hhalf (d cutoff : ℝ)
      (hball : ∀ u ∈ uIcc 0 cutoff, quadraticArc v ((u : ℂ) * (d : ℂ)) ∈ ball 0 (δ / 2)) :
      kernelHalfMoment A z j v b (n + D.shift + S.firstIndex) (S.saddle (n + D.shift)) k d cutoff =
        kernel r b A z j (n + D.shift + S.firstIndex)
          ((largeScale r (n + D.shift + S.firstIndex) : ℂ) * S.saddle (n + D.shift)) *
            D.halfMoment (largeScale r (n + D.shift + S.firstIndex)) k n d cutoff := by
    rw [kernelHalfMoment, halfMoment, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [hn _ (hball u hu)]
    simp only [momentAmplitude, Analytic.parameterShift_nat]
    ring
  simp only [localKernelMoment, localMoment, mul_sub]
  congr 1
  · exact hhalf _ _ (fun u hu => D.positive.inverseFamily.source_subset
      (D.positive.contour_in_source u
        (by simpa only [uIcc_of_le D.positive.cutoff_mem.1.le] using hu) n).1)
  · apply hhalf
    intro u hu
    simpa only [Complex.ofReal_neg] using D.negative.inverseFamily.source_subset
      (D.negative.contour_in_source u
        (by simpa only [uIcc_of_le D.negative.cutoff_mem.1.le] using hu) n).1

end CompactSaddleFamily.LocalParabolicData
end ThisWork
