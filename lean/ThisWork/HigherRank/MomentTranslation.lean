module

public import ThisWork.HigherRank.AbsoluteConvergence
public import ThisWork.HankelLinearity

/-! Exact changes of polynomial center. These identities apply before any
asymptotic estimate and in both directions, so recentering loses only a
polynomial factor. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set MeasureTheory

theorem kernel_change_center (r b q : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n : ℕ) (x : ℂ) :
    kernel r b A z j n x =
      Complex.exp ((Real.log z : ℂ) * (((b : ℂ) - q) * n)) * kernel r q A z j n x := by
  unfold kernel
  rw [show (Real.log z : ℂ) * ((b : ℂ) * n - x) =
    (Real.log z : ℂ) * (((b : ℂ) - q) * n) +
      (Real.log z : ℂ) * ((q : ℂ) * n - x) by ring, Complex.exp_add]
  ring

noncomputable def momentIntegral (r b : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n k : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * hankelIntegral (1 / 2) 1
    (fun x => ((b : ℂ) * n - x) ^ k * kernel r b A z j n x)

theorem momentIntegral_eq_component (r b : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (n : ℕ) (k : Fin r) :
    momentIntegral r b A z j n k.val = branchIntegral r b A z j n k := rfl

theorem momentIntegral_change_center {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i)
    (b q : ℕ) (z : ℝ) (j : ℤ) (n k : ℕ) :
    momentIntegral r b A z j n k =
      Complex.exp ((Real.log z : ℂ) * (((b : ℂ) - q) * n)) *
        ∑ i ∈ Finset.range (k + 1),
          ((((b : ℂ) - q) * n) ^ (k - i) * (k.choose i : ℂ)) *
            momentIntegral r q A z j n i := by
  let c : ℂ := Complex.exp ((Real.log z : ℂ) * (((b : ℂ) - q) * n))
  let a : ℕ → ℂ := fun i => (((b : ℂ) - q) * n) ^ (k - i) * (k.choose i : ℂ)
  have hconv (i : ℕ) : Analytic.HankelIntegrable (1 / 2) 1
      (fun x => ((q : ℂ) * n - x) ^ i * kernel r q A z j n x) :=
    weighted_hankel_absolutely_convergent hr hA q z j n i (by norm_num)
      (fun t => by nlinarith [mul_nonneg (hA t).le (Nat.cast_nonneg (α := ℝ) n)]) le_rfl
  have hid (x : ℂ) : ((b : ℂ) * n - x) ^ k * kernel r b A z j n x =
      c * ∑ i ∈ Finset.range (k + 1),
        a i * (((q : ℂ) * n - x) ^ i * kernel r q A z j n x) := by
    rw [kernel_change_center r b q A z j n x]
    rw [show (b : ℂ) * n - x = ((q : ℂ) * n - x) + (((b : ℂ) - q) * n) by ring,
      add_pow, Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [a, c]
    ring
  unfold momentIntegral
  simp_rw [hid]
  rw [Analytic.hankelIntegral_const_mul,
    Analytic.hankelIntegral_finset_sum _ (fun i _ => (hconv i).const_mul (a i))]
  simp_rw [Analytic.hankelIntegral_const_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [a, c]
  ring

end ThisWork.HigherRank
