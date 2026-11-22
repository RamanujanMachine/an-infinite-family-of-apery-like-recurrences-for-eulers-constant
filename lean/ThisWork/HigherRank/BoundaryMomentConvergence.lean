module

public import ThisWork.HigherRank.BoundaryGrowth
public import ThisWork.HigherRank.AbsoluteConvergence
public import ThisWork.HankelLinearity

/-! Absolute convergence and the integrated finite Fourier identity for every
component of the even-rank auxiliary boundary vector. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter MeasureTheory
open scoped Topology

theorem integrableOn_weighted_boundary_horizontal {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (m : ℕ) (z : ℝ) (n k : ℕ) {right y : ℝ} (hright : right < 1) (hy : |y| = 1) :
    IntegrableOn (fun u : ℝ => ((m : ℂ) * n - ((u : ℂ) + (y : ℂ) * Complex.I)) ^ k *
      boundaryKernel r m A z n ((u : ℂ) + (y : ℂ) * Complex.I)) (Iic right) := by
  apply Analytic.integrableOn_Iic_of_exp_bound
  · intro u hu
    have hs : (u : ℂ) + (y : ℂ) * Complex.I ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (by
        have hy0 : y ≠ 0 := by intro he; simp [he] at hy
        simpa using hy0))
    have hd := differentiableAt_boundaryKernel_of_slit hA m z n hs
      (by simpa [Complex.mul_re] using hu.trans_lt hright)
    exact ((by fun_prop : ContinuousAt (fun t : ℝ =>
      ((m : ℂ) * n - ((t : ℂ) + (y : ℂ) * Complex.I)) ^ k) u).mul
      (hd.continuousAt.comp (f := fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I)
        (by fun_prop))).continuousWithinAt
  have h := tendsto_neg_atBot_atTop.eventually
    (uniform_weighted_boundary_left_decay hr hA (H := 1) le_rfl half hrh m z n k 1)
  exact h.mono (fun u hu => by simpa using hu y hy.ge hy.le)

noncomputable def boundaryIntegral (r m : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (n : ℕ) : Fin r → ℂ := fun k =>
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((m : ℂ) * n - x) ^ k.val * boundaryKernel r m A z n x)

theorem boundaryIntegral_fourier {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (half : ℕ) (hrh : r = 2 * half)
    (m : ℕ) (z : ℝ) (n : ℕ) :
    (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) • boundaryIntegral r m A z n =
      ∑ i : Fin r, ((-1 : ℂ) ^ i.val * ((r - 1).choose i.val : ℂ)) •
        branchIntegral r m A z ((half : ℤ) - i.val) n := by
  funext k
  let c : ℕ → ℂ := fun i => (-1 : ℂ) ^ i * ((r - 1).choose i : ℂ)
  have hconv (i : ℕ) : Analytic.HankelIntegrable (1 / 2) 1
      (fun x => ((m : ℂ) * n - x) ^ k.val * kernel r m A z ((half : ℤ) - i) n x) :=
    weighted_hankel_absolutely_convergent hr hA m z _ n k.val (by norm_num)
      (fun t => by nlinarith [mul_nonneg (hA t).le (Nat.cast_nonneg (α := ℝ) n)]) le_rfl
  have he := Analytic.hankelIntegral_congr_on_trace (r := (1 / 2 : ℝ)) (h := (1 : ℝ))
    (by norm_num) (f := fun x => (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) *
      (((m : ℂ) * n - x) ^ k.val * boundaryKernel r m A z n x))
    (g := fun x => ∑ i ∈ Finset.range r, c i *
      (((m : ℂ) * n - x) ^ k.val * kernel r m A z ((half : ℤ) - i) n x)) (by
        intro x hx
        have hid := even_boundary_kernel_fourier hr half hrh m A z n (referenceContour_sin_ne_zero hx)
        calc
          _ = ((m : ℂ) * n - x) ^ k.val *
              ((2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) * boundaryKernel r m A z n x) := by ring
          _ = _ := by rw [hid, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; dsimp only [c]; ring)
  rw [Analytic.hankelIntegral_const_mul,
    Analytic.hankelIntegral_finset_sum _ (fun i _ => (hconv i).const_mul (c i))] at he
  simp_rw [Analytic.hankelIntegral_const_mul] at he
  change (2 * (Real.pi : ℂ) * Complex.I) ^ (r - 1) *
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _) = _
  rw [mul_left_comm, he, Finset.mul_sum, Finset.sum_range]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, branchIntegral]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [c]
  ring

end ThisWork.HigherRank
