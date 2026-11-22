module

public import ThisWork.HigherRank.ParabolicContour
public import ThisWork.HigherRank.KernelApproximation

/-! Uniform logarithmic norm comparisons for the actual Gamma kernel on
translated parabolic arcs, obtained by integrating its exact logarithmic
derivative. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set Filter

theorem norm_parabolic_tangent_le {a B b : ℝ} (ha : 0 ≤ a) (hb : |b| ≤ B) :
    ‖2 * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ 2 * (a + B) := by
  have h := norm_add_le (a : ℂ) ((b : ℂ) * Complex.I)
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha] at h
  calc
    _ = 2 * ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := by simp
    _ ≤ _ := by linarith

theorem uniform_kernelPhaseError_parabola {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (m : ℕ) (z : ℝ) (j : ℤ)
    {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ ≤ a ^ 2 / 8 →
      ∀ u v : ℝ, |u| ≤ B → |v| ≤ B →
        |kernelPhaseError r m A z j n (δ + parabolicPoint a v) -
          kernelPhaseError r m A z j n (δ + parabolicPoint a u)| ≤
            largeScale r n * C * smallParameter r n * |v - u| := by
  obtain ⟨D, hD, he⟩ := uniform_exactSaddleEquation_parabola hr hA z j ha B
  refine ⟨2 * (a + B) * D, by positivity, ?_⟩
  filter_upwards [he, eventually_translated_parabola_in_kernelDomain (by omega : 0 < r) hA ha,
    eventually_gt_atTop (0 : ℕ)] with n hn hdom hn0 δ hδ u v hu hv
  have hb (t : ℝ) (ht : t ∈ uIcc u v) : |t| ≤ B := by
    rcases mem_uIcc.mp ht with ht | ht
    · exact (abs_le_max_abs_abs ht.1 ht.2).trans (max_le hu hv)
    · exact (abs_le_max_abs_abs ht.1 ht.2).trans (max_le hv hu)
  have h := kernelPhaseError_curve_bound (m := m) hn0
    (γ := fun t => δ + parabolicPoint a t)
    (v := fun t => 2 * Complex.I * ((a : ℂ) + (t : ℂ) * Complex.I))
    (fun t _ => (hasDerivAt_parabolicPoint a t).const_add δ)
    (fun t ht => norm_parabolic_tangent_le ha.le (hb t ht))
    (fun t _ => region_mem_slitPlane (by positivity : 0 < a ^ 2 / 4)
      (by positivity : 0 < a ^ 2 / 4) (translated_parabola_region ha hδ t))
    (fun t _ => hdom δ hδ t) (fun t ht => hn δ hδ t (hb t ht))
  convert h using 1
  ring

end ThisWork.HigherRank
