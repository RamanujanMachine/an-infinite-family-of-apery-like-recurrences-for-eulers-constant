module

public import ThisWork.QuadraticPhase
public import ThisWork.CompactParameterTools
public import Neuschel.QuadraticCurves

/-! Uniform local Laplace contours on the same parabolas used for the global
phase bounds. The curved-contour expansion retains the actual Jacobian. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric
open scoped Topology OnePoint

noncomputable def quadraticArc (v t : ℂ) : ℂ := t * v - t ^ 2

@[simp] theorem quadraticArc_zero (v : ℂ) : quadraticArc v 0 = 0 := by simp [quadraticArc]

theorem continuous_quadraticArc (v : ℂ) : Continuous (quadraticArc v) := by
  unfold quadraticArc
  fun_prop

theorem hasDerivAt_quadraticArc (v t : ℂ) :
    HasDerivAt (quadraticArc v) (v - 2 * t) t := by
  convert ((hasDerivAt_id t).mul_const v).sub ((hasDerivAt_id t).pow 2) using 1
  · rfl
  · simp

theorem hasDerivAt_scaled_quadraticArc (v : ℂ) (d u : ℝ) :
    HasDerivAt (fun t : ℝ => quadraticArc v ((t : ℂ) * (d : ℂ)))
      ((d : ℂ) * (v - 2 * ((u : ℂ) * (d : ℂ)))) u := by
  have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * (d : ℂ)) (d : ℂ) u := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasDerivAt.mul_const (d : ℂ))
  exact Neuschel.hasDerivAt_primitive_comp (f := fun t => v - 2 * t)
    (hasDerivAt_quadraticArc v ((u : ℂ) * (d : ℂ))) hlin

namespace CompactSaddleFamily

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}
    (S : CompactSaddleFamily r A z j ζ δ)

theorem exists_shift_quadratic_positive {v : ℂ}
    (hpos : 0 < (S.phaseCoefficients 0 ∞ * v ^ 2).re) :
    ∃ N : ℕ, ∀ q : OnePoint ℕ,
      0 < (S.phaseCoefficients 0 (Analytic.parameterShift N q) * v ^ 2).re := by
  have he : ∀ᶠ k : ℕ in atTop, 0 < (S.phaseCoefficients 0 k * v ^ 2).re :=
    ((OnePoint.continuous_iff_from_nat _).mp
      (Complex.continuous_re.comp ((S.continuous_phaseCoefficients 0).mul continuous_const))).eventually
        (lt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun q => ?_⟩
  cases q with
  | infty => exact hpos
  | coe k => exact hN (k + N) (Nat.le_add_left N k)

theorem exists_uniform_parabolic_positivity {v : ℂ}
    (hpos : 0 < (S.phaseCoefficients 0 ∞ * v ^ 2).re) :
    ∃ N : ℕ, ∃ R > 0, ∀ u : ℝ, |u| < R → u ≠ 0 → ∀ q : OnePoint ℕ,
      quadraticArc v u ∈ ball 0 (δ / 2) ∧
        0 < (S.phase (quadraticArc v u) (Analytic.parameterShift N q)).re := by
  obtain ⟨N, hN⟩ := S.exists_shift_quadratic_positive hpos
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, quadraticArc v t ∈ ball 0 (δ / 2) := by
    apply (continuous_quadraticArc v).continuousAt.tendsto.eventually
    rw [quadraticArc_zero]
    filter_upwards [ball_mem_nhds (0 : ℂ) (half_pos S.radius_pos)] with t ht
    exact ht
  obtain ⟨R₀, hR₀, hmap⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let H : ℂ → OnePoint ℕ → ℂ := fun t q =>
    S.quadraticFactor (quadraticArc v t) (Analytic.parameterShift N q) * (v - t) ^ 2
  have hg : Continuous (fun w : ℂ × OnePoint ℕ =>
      (quadraticArc v w.1, Analytic.parameterShift N w.2)) :=
    ((continuous_quadraticArc v).comp continuous_fst).prodMk
      ((Analytic.parameterShift N).continuous.comp continuous_snd)
  have hH : ContinuousOn (Function.uncurry H) (ball (0 : ℂ) R₀ ×ˢ univ) :=
    ((S.quadraticFactor_regular).1.comp hg.continuousOn
      (fun w hw => ⟨hmap w.1 hw.1, mem_univ _⟩)).mul (by fun_prop)
  obtain ⟨R, hR, hsub, hpositive⟩ := Neuschel.exists_uniform_mapsTo_nhds isOpen_ball
    (mem_ball_self hR₀) hH (V := {w : ℂ | 0 < w.re})
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun q => by simpa only [Set.mem_ofPred_eq, H, quadraticArc_zero, S.quadraticFactor_center, sub_zero] using hN q)
  refine ⟨N, R, hR, fun u hu hune q => ?_⟩
  have hut : (u : ℂ) ∈ ball 0 R := by simpa only [mem_ball, dist_zero_right, Complex.norm_real,
    Real.norm_eq_abs] using hu
  refine ⟨hmap u (hsub hut), ?_⟩
  have he : S.phase (quadraticArc v u) (Analytic.parameterShift N q) =
      (u : ℂ) ^ 2 * H u q := by
    rw [S.phase_eq_quadratic]
    dsimp only [quadraticArc, H]
    ring
  rw [he, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_pos (sq_pos_of_ne_zero hune) (hpositive q hut)

theorem exists_local_parabolic_models {v : ℂ}
    (hpos : 0 < (S.phaseCoefficients 0 ∞ * v ^ 2).re) :
    ∃ N : ℕ, ∃ d > 0, ∀ e : ℝ, e = 1 ∨ e = -1 →
      Nonempty (Neuschel.LocalContourModel 2 0 (((e * d : ℝ) : ℂ) * v)
        (fun q => S.phaseCoefficients 0 (Analytic.parameterShift N q))
        (fun t q => S.phase t (Analytic.parameterShift N q)) (ball 0 (δ / 2))
        (fun u : ℝ => quadraticArc v ((u : ℂ) * ((e * d : ℝ) : ℂ)))) := by
  obtain ⟨N, R, hR, hb⟩ := S.exists_uniform_parabolic_positivity hpos
  have hv : v ≠ 0 := by intro he; simp [he] at hpos
  refine ⟨N, R / 2, half_pos hR, fun e he => ?_⟩
  have hc : Continuous (fun w : ℂ × OnePoint ℕ => (w.1, Analytic.parameterShift N w.2)) :=
    continuous_fst.prodMk ((Analytic.parameterShift N).continuous.comp continuous_snd)
  have hP := S.continuous_phase.comp
    (s := ball (0 : ℂ) (δ / 2) ×ˢ (univ : Set (OnePoint ℕ)))
    hc.continuousOn (fun w hw => ⟨hw.1, mem_univ _⟩)
  change ContinuousOn (Function.uncurry (fun t q => S.phase t (Analytic.parameterShift N q)))
    (ball (0 : ℂ) (δ / 2) ×ˢ univ) at hP
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hγ : HasDerivWithinAt
      (fun u : ℝ => quadraticArc v ((u : ℂ) * ((e * (R / 2) : ℝ) : ℂ)))
      (((e * (R / 2) : ℝ) : ℂ) * v) (Ici 0) 0 := by
    simpa only [Complex.ofReal_zero, zero_mul, mul_zero, sub_zero] using
      (hasDerivAt_scaled_quadraticArc v (e * (R / 2)) 0).hasDerivWithinAt
  apply Neuschel.exists_localContourModel isOpen_ball (mem_ball_self (half_pos S.radius_pos))
    (by decide) hP (fun q => S.differentiableOn_phase (Analytic.parameterShift N q))
    (fun q => S.phase_expansion (Analytic.parameterShift N q))
    (fun q => S.phaseCoefficients_zero_ne (Analytic.parameterShift N q)) hγ (by simp)
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero he0 (half_pos hR).ne')) hv)
  intro u hu q
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have hsmall : |e * (R / 2) * u| < R := by
    rw [abs_mul, abs_mul, heabs, abs_of_pos (half_pos hR), abs_of_pos hu.1]
    nlinarith [mul_lt_mul_of_pos_left hu.2 hR]
  have harg : (u : ℂ) * ((e * (R / 2) : ℝ) : ℂ) = ((e * (R / 2) * u : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [phase_zero, sub_zero, harg] using
    (hb (e * (R / 2) * u) hsmall (mul_ne_zero (mul_ne_zero he0 (half_pos hR).ne') hu.1.ne') q).2

end CompactSaddleFamily
end ThisWork
