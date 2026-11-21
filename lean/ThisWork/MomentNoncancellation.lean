module

public import ThisWork.Noncancellation
public import ThisWork.VectorMomentBounds
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Polynomial conditioning of the moment coordinates upgrades limiting
Vandermonde independence to a lower bound for every coefficient vector. -/

@[expose] public section
namespace ThisWork.Analytic

open Filter
open scoped Topology

theorem norm_momentTransform_le {n : ℕ} {R : ℝ} (hn : 1 ≤ n) (hR : 1 ≤ R)
    (v : Fin 3 → ℂ) : ‖momentTransform n R v‖ ≤ 4 * (n : ℝ) ^ 2 * ‖v‖ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  fin_cases k
  · change ‖v 0‖ ≤ _
    nlinarith [norm_le_pi_norm v 0, norm_nonneg v]
  · change ‖((n : ℂ) * v 0 - v 1) / (R : ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_of_nonneg hR0.le]
    have hnum : ‖(n : ℂ) * v 0 - v 1‖ ≤ ((n : ℝ) + 1) * ‖v‖ := by
      have h := norm_sub_le ((n : ℂ) * v 0) (v 1)
      rw [norm_mul, Complex.norm_natCast] at h
      nlinarith [norm_le_pi_norm v 0, norm_le_pi_norm v 1,
        mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (Nat.cast_nonneg n)]
    exact (div_le_self (norm_nonneg _) hR).trans (hnum.trans (by nlinarith [norm_nonneg v]))
  · change ‖((n : ℂ) ^ 2 * v 0 - 2 * (n : ℂ) * v 1 + v 2) / (R : ℂ) ^ 2‖ ≤ _
    rw [norm_div, norm_pow, Complex.norm_of_nonneg hR0.le]
    have hnum : ‖(n : ℂ) ^ 2 * v 0 - 2 * (n : ℂ) * v 1 + v 2‖ ≤
        ((n : ℝ) ^ 2 + 2 * n + 1) * ‖v‖ := by
      calc
        _ ≤ ‖(n : ℂ) ^ 2 * v 0‖ + ‖2 * (n : ℂ) * v 1‖ + ‖v 2‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ = (n : ℝ) ^ 2 * ‖v 0‖ + 2 * n * ‖v 1‖ + ‖v 2‖ := by
          simp only [norm_mul, norm_pow, Complex.norm_natCast, RCLike.norm_two]
        _ ≤ _ := by nlinarith [norm_le_pi_norm v 2,
          mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (sq_nonneg (n : ℝ)),
          mul_le_mul_of_nonneg_left (norm_le_pi_norm v 1) (show (0 : ℝ) ≤ 2 * n by positivity)]
    exact (div_le_self (norm_nonneg _) (by nlinarith : 1 ≤ R ^ 2)).trans
      (hnum.trans (by nlinarith [norm_nonneg v]))

theorem eventually_noncancellation_of_rank_three_moments {ζ : Fin 3 → ℂ}
    (hζ : Function.Injective ζ) {V : Fin 3 → ℕ → Fin 3 → ℂ}
    (b : ℕ → Fin 3 → ℂ) (hb : ∀ᶠ n : ℕ in atTop, ∀ i, b n i ≠ 0)
    (hlim : ∀ i k, Tendsto (fun n => b n i * momentTransform n (largeScale n) (V i n) k)
      atTop (𝓝 (ζ i ^ k.val))) :
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ a : Fin 3 → ℂ, ∀ j : Fin 3,
      ‖a j‖ * ‖V j n‖ ≤ K * (n : ℝ) ^ 4 * ‖∑ i, a i • V i n‖ := by
  let T (n : ℕ) := (momentTransform n (largeScale n)).toContinuousLinearMap
  obtain ⟨C, hC, hnc⟩ := eventually_noncancellation_of_normalized_moments hζ T b hb hlim
  let L : Fin 3 → Fin 3 → ℂ := fun i k => ζ i ^ k.val
  have hconv : Tendsto (fun n => fun i k => b n i * momentTransform n (largeScale n) (V i n) k)
      atTop (𝓝 L) := tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hlim i))
  let M := ‖L‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨16 * M * C, by positivity, ?_⟩
  filter_upwards [hnc, hb, hconv.norm.eventually_lt_const (lt_add_one ‖L‖),
    largeScale_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hn hbn hnm hR hn1 a j
  have hR0 : 0 < largeScale n := zero_lt_one.trans_le hR
  have hRn : largeScale n ≤ (n : ℝ) := Real.rpow_le_self_of_one_le
    (by exact_mod_cast hn1) (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hcomponents (k : Fin 3) : ‖b n j * momentTransform n (largeScale n) (V j n) k‖ ≤ M :=
    (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ j).trans hnm.le)
  have hV := norm_vector_le_of_normalized_moments hn1 hR0 hRn hM.le (hbn j) (V j n) hcomponents
  have hT : ‖T n‖ ≤ 4 * (n : ℝ) ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound (T n) (by positivity)
    exact norm_momentTransform_le hn1 hR
  have hcoef := (norm_le_pi_norm (fun i => a i / b n i) j).trans (hn a)
  rw [norm_div] at hcoef
  have hprod : ‖a j‖ * ‖(b n j)⁻¹‖ ≤ C * (4 * (n : ℝ) ^ 2) * ‖∑ i, a i • V i n‖ := by
    rw [norm_inv, ← div_eq_mul_inv]
    exact hcoef.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT hC.le) (norm_nonneg _))
  calc
    _ ≤ ‖a j‖ * (4 * (n : ℝ) ^ 2 * M * ‖(b n j)⁻¹‖) :=
      mul_le_mul_of_nonneg_left hV (norm_nonneg _)
    _ = (4 * (n : ℝ) ^ 2 * M) * (‖a j‖ * ‖(b n j)⁻¹‖) := by ring
    _ ≤ (4 * (n : ℝ) ^ 2 * M) * (C * (4 * (n : ℝ) ^ 2) * ‖∑ i, a i • V i n‖) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

end ThisWork.Analytic
