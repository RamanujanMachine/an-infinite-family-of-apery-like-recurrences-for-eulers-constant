module

public import ThisWork.MomentIndependence
public import Mathlib.Analysis.Matrix.Normed

/-! Uniform noncancellation for matrices converging to a nonsingular limit.
The bound is uniform in the coefficient vector, which may depend on `n`. -/

@[expose] public section
namespace ThisWork.Analytic

open Filter Matrix
open scoped Topology Matrix.Norms.Operator

theorem eventually_uniform_lower_bound {d : ℕ}
    {A : ℕ → Matrix (Fin d) (Fin d) ℂ} {L : Matrix (Fin d) (Fin d) ℂ}
    (hA : Tendsto A atTop (𝓝 L)) (hL : L.det ≠ 0) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℂ,
      ‖v‖ ≤ C * ‖(A n) *ᵥ v‖ := by
  have hinv : Tendsto (fun n => (A n)⁻¹) atTop (𝓝 L⁻¹) := by
    apply (continuousAt_matrix_inv L ?_).tendsto.comp hA
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hL)
  have hdet : ∀ᶠ n : ℕ in atTop, (A n).det ≠ 0 :=
    ((continuous_id.matrix_det.continuousAt.tendsto.comp hA).eventually
      (isOpen_ne.mem_nhds hL))
  refine ⟨‖L⁻¹‖ + 1, by positivity, ?_⟩
  filter_upwards [hinv.norm.eventually_lt_const (lt_add_one ‖L⁻¹‖), hdet] with n hn hd
  intro v
  calc
    ‖v‖ = ‖(A n)⁻¹ *ᵥ ((A n) *ᵥ v)‖ := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
        Matrix.one_mulVec]
    _ ≤ ‖(A n)⁻¹‖ * ‖(A n) *ᵥ v‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ (‖L⁻¹‖ + 1) * ‖(A n) *ᵥ v‖ :=
      mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- Distinct limiting saddle moments prevent cancellation uniformly over all
coefficient vectors, including vectors varying with `n`. -/
theorem eventually_noncancellation_of_moment_limits {d : ℕ} {ζ : Fin d → ℂ}
    (hζ : Function.Injective ζ) {A : ℕ → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ i k, Tendsto (fun n => A n i k) atTop (𝓝 (ζ i ^ k.val))) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ a : Fin d → ℂ,
      ‖a‖ ≤ C * ‖fun k => ∑ i, a i * A n i k‖ := by
  have hlim : Tendsto A atTop (𝓝 (Matrix.vandermonde ζ)) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun k => hA i k))
  have ht : Tendsto (fun n => (A n).transpose) atTop
      (𝓝 (Matrix.vandermonde ζ).transpose) :=
    (continuous_id.matrix_transpose.tendsto _).comp hlim
  have hd : (Matrix.vandermonde ζ).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hζ
  obtain ⟨C, hC, he⟩ := eventually_uniform_lower_bound ht hd
  refine ⟨C, hC, he.mono (fun n hn a => ?_)⟩
  have hvec : (A n).transpose *ᵥ a = (fun k => ∑ i, a i * A n i k) := by
    funext k
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, mul_comm]
  rw [← hvec]
  exact hn a

/-- Version for rescaled integral vectors. The only loss is the operator norm
of the common moment transform; the normalizers remain explicit. -/
theorem eventually_noncancellation_of_normalized_moments {d : ℕ} {ζ : Fin d → ℂ}
    (hζ : Function.Injective ζ) {V : Fin d → ℕ → Fin d → ℂ}
    (T : ℕ → (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (b : ℕ → Fin d → ℂ)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ i, b n i ≠ 0)
    (hlim : ∀ i k, Tendsto (fun n => b n i * T n (V i n) k) atTop (𝓝 (ζ i ^ k.val))) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ a : Fin d → ℂ,
      ‖fun i => a i / b n i‖ ≤
        C * ‖T n‖ * ‖∑ i, a i • V i n‖ := by
  obtain ⟨C, hC, he⟩ := eventually_noncancellation_of_moment_limits hζ hlim
  refine ⟨C, hC, ?_⟩
  filter_upwards [he, hb] with n hn hbn
  intro a
  have hsum : (fun k => ∑ i, (a i / b n i) * (b n i * T n (V i n) k)) =
      T n (∑ i, a i • V i n) := by
    funext k
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, div_mul_cancel₀ _ (hbn i)]
  have hbound := hn (fun i => a i / b n i)
  rw [hsum] at hbound
  calc
    _ ≤ C * ‖T n (∑ i, a i • V i n)‖ := hbound
    _ ≤ C * (‖T n‖ * ‖∑ i, a i • V i n‖) :=
      mul_le_mul_of_nonneg_left ((T n).le_opNorm _) hC.le
    _ = _ := by ring

end ThisWork.Analytic
