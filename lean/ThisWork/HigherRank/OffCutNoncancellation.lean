module

public import ThisWork.HigherRank.OffCutIndependence
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Uniform polynomial lower bounds on the off-cut subspace. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter
open scoped Topology

theorem norm_firstPowerMomentTransform_le {r d n : ℕ} (hd : d ≤ r)
    (hR : 1 ≤ largeScale r n) (v : Fin r → ℂ) :
    ‖firstPowerMomentTransform hd n v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro k
  exact (norm_le_pi_norm (powerMomentTransform r n v) (k.castLE hd)).trans
    (norm_powerMomentTransform_le hR v)

theorem offCut_zeroCenter_noncancellation {r d : ℕ} (hr : 3 ≤ r) (hd : d ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (J : Fin d → ℤ) (θ : Fin d → ℝ) (hθ : ∀ i, θ i ∈ Ioo (-Real.pi) Real.pi)
    (hj : ∀ i, (r : ℝ) * θ i = -2 * Real.pi * J i)
    (hinj : Function.Injective θ) :
    ∃ K > 0, ∀ᶠ n : ℕ in atTop, ∀ a : Fin d → ℂ, ∀ j : Fin d,
      ‖a j‖ * ‖branchIntegral r 0 A z (J j) n‖ ≤
        K * (n : ℝ) ^ (r - 1) * ‖∑ i, a i • branchIntegral r 0 A z (J i) n‖ := by
  classical
  let D : ∀ i, OffCutLocalData r A z (J i) (θ i) := fun i =>
    Classical.choice (exists_offCutLocalData hr hA hz (J i) (hθ i) (hj i))
  let b : ℕ → Fin d → ℂ := fun n i => (D i).normalizingScalar n
  let T (n : ℕ) := (firstPowerMomentTransform hd n).toContinuousLinearMap
  have hζ : Function.Injective (fun i => (saddleScale r A z : ℂ) * Phase.rho (θ i)) := by
    intro i k hik
    apply hinj
    apply rho_injective_on_principal (hθ i) (hθ k)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (saddleScale_pos hA hz).ne') hik
  have hb : ∀ᶠ n : ℕ in atTop, ∀ i, b n i ≠ 0 :=
    Filter.eventually_all.mpr (fun i => (D i).eventually_normalizingScalar_ne_zero (by omega) hA)
  obtain ⟨C, hC, hnc⟩ := Analytic.eventually_noncancellation_of_normalized_moments hζ T b hb
    (fun i k => (D i).normalized_originalMoment_tendsto hr hA hz (k.castLE hd))
  let L : Fin d → Fin r → ℂ := fun i k => ((saddleScale r A z : ℂ) * Phase.rho (θ i)) ^ k.val
  have hconv : Tendsto (fun n => fun i k => b n i * powerMomentTransform r n
      (branchIntegral r 0 A z (J i) n) k) atTop (𝓝 L) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr
      ((D i).normalized_originalMoment_tendsto hr hA hz))
  let M := ‖L‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M * C, by positivity, ?_⟩
  filter_upwards [hnc, hb, hconv.norm.eventually_lt_const (lt_add_one ‖L‖),
    (largeScale_tendsto (show 1 < r by omega)).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hn hbn hnm hR hn1 a j
  have hcomponents (k : Fin r) :
      ‖b n j * powerMomentTransform r n (branchIntegral r 0 A z (J j) n) k‖ ≤ M :=
    (norm_le_pi_norm _ k).trans ((norm_le_pi_norm _ j).trans hnm.le)
  have hV := norm_vector_le_of_normalized_power_moments (by omega : 0 < r) hn1 hR
    hM.le (hbn j) (branchIntegral r 0 A z (J j) n) hcomponents
  have hT : ‖T n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [T, LinearMap.coe_toContinuousLinearMap', one_mul] using
      norm_firstPowerMomentTransform_le hd hR v
  have hcoef := (norm_le_pi_norm (fun i => a i / b n i) j).trans (hn a)
  rw [norm_div] at hcoef
  have hprod : ‖a j‖ * ‖(b n j)⁻¹‖ ≤ C * ‖∑ i, a i • branchIntegral r 0 A z (J i) n‖ := by
    rw [norm_inv, ← div_eq_mul_inv]
    exact hcoef.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hC.le) (norm_nonneg _))
  calc
    _ ≤ ‖a j‖ * ((n : ℝ) ^ (r - 1) * M * ‖(b n j)⁻¹‖) :=
      mul_le_mul_of_nonneg_left hV (norm_nonneg _)
    _ = ((n : ℝ) ^ (r - 1) * M) * (‖a j‖ * ‖(b n j)⁻¹‖) := by ring
    _ ≤ ((n : ℝ) ^ (r - 1) * M) *
        (C * ‖∑ i, a i • branchIntegral r 0 A z (J i) n‖) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

end ThisWork.HigherRank
