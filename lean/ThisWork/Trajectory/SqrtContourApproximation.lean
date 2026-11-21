module

public import ThisWork.Trajectory.SqrtApproximation
public import ThisWork.ImaginaryDigamma

/-! Uniform saddle-equation approximation on bounded contour regions,
including both sides of the imaginary axis. -/

public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

theorem uniform_exactSqrtEquation_region {d : ℕ} {A₁ A₂ z κ η M ε : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hκ : 0 < κ) (hη : 0 < η) (hε : 0 < ε) (j : Branch) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ s : ℂ, ‖s‖ ≤ M → κ ≤ s.re ∨ η ≤ |s.im| →
      ‖exactSqrtEquation d A₁ A₂ z j n s - limitingSqrtEquation d A₁ A₂ z j s‖ ≤ ε := by
  let L := fun a : ℝ => (11 + 3 * M) / (2 * a)
  let C := L d + 2 / d + L A₁ + L A₂
  have hsmall : ∀ᶠ n : ℕ in atTop, C / sqrtScale n ≤ ε / 2 := by
    have hlim : Tendsto (fun n => C / sqrtScale n) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
        (tendsto_inv_atTop_zero.comp sqrtScale_tendsto).const_mul C
    exact (hlim.eventually (gt_mem_nhds (half_pos hε))).mono (fun _ h => h.le)
  filter_upwards [sqrtScale_tendsto.eventually
    (Analytic.uniform_scaled_digamma_region hκ hη (show 0 < ε / 4 by positivity)),
    eventually_right_factor_conditions (Nat.cast_pos.mpr hd) M,
    eventually_right_factor_conditions h₁ M, eventually_right_factor_conditions h₂ M,
    hsmall, eventually_ge_atTop (1 : ℕ)] with n hψ hD hA₁ hA₂ herr hn
  refine ⟨by omega, fun s hs hregion => ?_⟩
  have hs0 : s ≠ 0 := by
    intro he
    rw [he, Complex.zero_re, Complex.zero_im, abs_zero] at hregion
    rcases hregion with h | h <;> linarith
  have hb := norm_exactSqrtEquation_sub_limit_le hd h₁ h₂ hz j (by omega : 0 < n)
    hs hs0 hD.1 hA₁.1 hA₂.1 hD.2 hA₁.2 hA₂.2
  have hInv : 2 / ((d : ℝ) * n) ≤ (2 / d) * (1 / sqrtScale n) := by
    calc
      _ = (2 / d) * (1 / (n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_nat_le_inv_sqrtScale hn) (by positivity)
  have hbound := hb.trans (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (hψ.2 s hregion) (by norm_num))
      (add_le_add (affineError_le_inv_sqrtScale (Nat.cast_pos.mpr hd) hn M) hInv))
    (affineError_le_inv_sqrtScale h₁ hn M)) (affineError_le_inv_sqrtScale h₂ hn M))
  calc
    _ ≤ _ := hbound
    _ = ε / 2 + C / sqrtScale n := by dsimp only [C, L]; ring
    _ ≤ ε := by linarith

end ThisWork.Trajectory
