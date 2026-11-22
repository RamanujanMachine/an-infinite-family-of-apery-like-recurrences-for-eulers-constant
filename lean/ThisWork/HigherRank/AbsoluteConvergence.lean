module

public import ThisWork.HigherRank.HankelTails
public import ThisWork.AbsoluteConvergence

/-! Absolute convergence of the arbitrary-rank Mellin--Barnes integrals,
including all polynomial moments appearing in the original vector functions. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter MeasureTheory
open scoped Topology

theorem horizontal_mem_kernelDomain {r : ℕ} {A : Fin (r - 1) → ℝ}
    {n : ℕ} {right y u : ℝ} (hright : ∀ i, right < A i * n + 1)
    (hy : y ≠ 0) (hu : u ≤ right) :
    (u : ℂ) + (y : ℂ) * Complex.I ∈ kernelDomain r A n := by
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hy)), ?_⟩
  intro i
  simpa [Complex.mul_re] using hu.trans_lt (hright i)

theorem differentiableOn_weighted_kernel (r m : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n k : ℕ) :
    DifferentiableOn ℂ (fun x => ((m : ℂ) * n - x) ^ k * kernel r m A z j n x) (kernelDomain r A n) :=
  (by fun_prop : DifferentiableOn ℂ (fun x : ℂ => ((m : ℂ) * n - x) ^ k) (kernelDomain r A n)).mul
    (fun _ hx => (differentiableAt_kernel m z j n hx).differentiableWithinAt)

theorem integrableOn_weighted_kernel_horizontal {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    {right y : ℝ} (hright : ∀ i, right < A i * n + 1) (hy : 1 ≤ |y|) :
    IntegrableOn (fun u : ℝ => ((m : ℂ) * n - ((u : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      kernel r m A z j n ((u : ℂ) + (y : ℂ) * Complex.I)) (Iic right) := by
  apply Analytic.integrableOn_Iic_of_exp_bound
  · exact (differentiableOn_weighted_kernel r m A z j n k).continuousOn.comp
      (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I)).continuousOn
      (fun _ hu => horizontal_mem_kernelDomain hright
        (by intro he; norm_num [he] at hy) hu)
  have h := tendsto_neg_atBot_atTop.eventually (uniform_weighted_kernel_left_decay hr hA hy m z j n k 1)
  exact h.mono fun u hu => by simpa using hu y hy le_rfl

theorem intervalIntegrable_weighted_kernel_vertical {r : ℕ} {A : Fin (r - 1) → ℝ}
    (m : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ) {right : ℝ} (hright0 : 0 < right)
    (hright : ∀ i, right < A i * n + 1) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => Complex.I *
      (((m : ℂ) * n - ((right : ℂ) + (y : ℂ) * Complex.I)) ^ k *
        kernel r m A z j n ((right : ℂ) + (y : ℂ) * Complex.I))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_const.mul ((differentiableOn_weighted_kernel r m A z j n k).continuousOn.comp
    (by fun_prop : Continuous (fun y : ℝ => (right : ℂ) + (y : ℂ) * Complex.I)).continuousOn
    (fun _ _ => ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa [Complex.mul_re] using hright0)),
      fun i => by simpa [Complex.mul_re] using hright i⟩))

theorem weighted_hankel_absolutely_convergent {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    {right height : ℝ} (hright0 : 0 < right) (hright : ∀ i, right < A i * n + 1) (hh : 1 ≤ height) :
    IntegrableOn (fun u : ℝ => ((m : ℂ) * n - ((u : ℂ) - (height : ℂ) * Complex.I)) ^ k *
      kernel r m A z j n ((u : ℂ) - (height : ℂ) * Complex.I)) (Iic right) ∧
    IntervalIntegrable (fun y : ℝ => Complex.I *
      (((m : ℂ) * n - ((right : ℂ) + (y : ℂ) * Complex.I)) ^ k *
        kernel r m A z j n ((right : ℂ) + (y : ℂ) * Complex.I))) volume (-height) height ∧
    IntegrableOn (fun u : ℝ => ((m : ℂ) * n - ((u : ℂ) + (height : ℂ) * Complex.I)) ^ k *
      kernel r m A z j n ((u : ℂ) + (height : ℂ) * Complex.I)) (Iic right) := by
  refine ⟨?_, intervalIntegrable_weighted_kernel_vertical m z j n k hright0 hright (-height) height,
    integrableOn_weighted_kernel_horizontal hr hA m z j n k hright
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ height)] using hh)⟩
  simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using
    integrableOn_weighted_kernel_horizontal hr hA m z j n k hright (y := -height)
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ height)] using hh)

theorem tendsto_left_bridge_zero {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) {H a b : ℝ} (hH : 1 ≤ H)
    (m : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ)
    (hstrip : ∀ y ∈ uIcc a b, 1 ≤ |y| ∧ |y| ≤ H) :
    Tendsto (fun T : ℝ => ∫ y in a..b, Complex.I *
      (((m : ℂ) * n - (-(T : ℂ) + (y : ℂ) * Complex.I)) ^ k *
        kernel r m A z j n (-(T : ℂ) + (y : ℂ) * Complex.I))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun T => Real.exp (-T) * |b - a|)
  · filter_upwards [uniform_weighted_kernel_left_decay hr hA hH m z j n k 1] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    simpa only [norm_mul, Complex.norm_I, one_mul, neg_mul, one_mul] using
      hT y (hstrip y (uIoc_subset_uIcc hy)).1 (hstrip y (uIoc_subset_uIcc hy)).2
  · simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const |b - a|

end ThisWork.HigherRank
