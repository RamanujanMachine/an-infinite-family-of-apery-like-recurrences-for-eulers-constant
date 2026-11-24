module

public import ThisWork.HigherRank.LocalPhase
public import ThisWork.LogNorm

/-! Integrating quantitative saddle-equation errors along curved contours. -/

@[expose] public section
namespace ThisWork.HigherRank

open Set

noncomputable def limitingPhase (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (s : ℂ) : ℂ := s * (limitingEquation r A z j s - r)

theorem hasDerivAt_limitingPhase (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) {s : ℂ} (hs : s ∈ Complex.slitPlane) :
    HasDerivAt (limitingPhase r A z j) (limitingEquation r A z j s) s := by
  convert (hasDerivAt_id s).mul
    ((hasDerivAt_limitingEquation r A z j hs).sub_const (r : ℂ)) using 1
  · rfl
  · simp only [one_mul, id_eq, mul_div_cancel₀ _ (Complex.slitPlane_ne_zero hs), sub_add_cancel]

noncomputable def kernelPhaseError (r b : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ)
    (j : ℤ) (n : ℕ) (s : ℂ) : ℝ :=
  Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * s)‖ -
    largeScale r n * (limitingPhase r A z j s).re

theorem hasDerivAt_kernelPhaseError_comp {r b : ℕ} {A : Fin (r - 1) → ℝ}
    {z : ℝ} {j : ℤ} {n : ℕ} {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hslit : γ t ∈ Complex.slitPlane)
    (hdom : (largeScale r n : ℂ) * γ t ∈ kernelDomain r A n) :
    HasDerivAt (fun u => kernelPhaseError r b A z j n (γ u))
      (largeScale r n * (v * (exactSaddleEquation r A z j n (γ t) -
        limitingEquation r A z j (γ t))).re) t := by
  have hf : DifferentiableOn ℂ (kernel r b A z j n) (kernelDomain r A n) :=
    fun x hx => (differentiableAt_kernel b z j n hx).differentiableWithinAt
  have hK := Analytic.hasDerivAt_log_norm_comp (isOpen_kernelDomain r A n) hf
    (fun x hx => kernel_ne_zero b z j n hx) (hγ.const_mul (largeScale r n : ℂ)) hdom
  have hφ := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (Neuschel.hasDerivAt_primitive_comp (hasDerivAt_limitingPhase r A z j hslit) hγ)).const_mul
      (largeScale r n)
  convert hK.sub hφ using 1
  · rfl
  · rw [← exactSaddleEquation_eq_logDeriv b z j n hdom]
    simp only [Complex.reCLM_apply, mul_sub, Complex.sub_re, mul_assoc,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The tangent may vary along the curve. This includes the parabolic arcs,
as well as the straight segments used in the rank-three development. -/
theorem kernelPhaseError_curve_bound {r b : ℕ} {A : Fin (r - 1) → ℝ}
    {z : ℝ} {j : ℤ} {n : ℕ} (hn : 0 < n)
    {γ v : ℝ → ℂ} {a auxB ε L : ℝ}
    (hγ : ∀ t ∈ uIcc a auxB, HasDerivAt γ (v t) t)
    (hv : ∀ t ∈ uIcc a auxB, ‖v t‖ ≤ L)
    (hslit : ∀ t ∈ uIcc a auxB, γ t ∈ Complex.slitPlane)
    (hdom : ∀ t ∈ uIcc a auxB, (largeScale r n : ℂ) * γ t ∈ kernelDomain r A n)
    (herr : ∀ t ∈ uIcc a auxB,
      ‖exactSaddleEquation r A z j n (γ t) - limitingEquation r A z j (γ t)‖ ≤ ε) :
    |kernelPhaseError r b A z j n (γ auxB) - kernelPhaseError r b A z j n (γ a)| ≤
      largeScale r n * L * ε * |auxB - a| := by
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hb (t : ℝ) (ht : t ∈ uIcc a auxB) :
      ‖largeScale r n * (v t * (exactSaddleEquation r A z j n (γ t) -
        limitingEquation r A z j (γ t))).re‖ ≤ largeScale r n * L * ε := by
    calc
      _ = largeScale r n * |(v t * (exactSaddleEquation r A z j n (γ t) -
          limitingEquation r A z j (γ t))).re| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hR]
      _ ≤ largeScale r n * ‖v t * (exactSaddleEquation r A z j n (γ t) -
          limitingEquation r A z j (γ t))‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hR.le
      _ = largeScale r n * (‖v t‖ * ‖exactSaddleEquation r A z j n (γ t) -
          limitingEquation r A z j (γ t)‖) := by rw [norm_mul]
      _ ≤ largeScale r n * (L * ε) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hv t ht) (herr t ht) (norm_nonneg _) ((norm_nonneg _).trans (hv t ht))) hR.le
      _ = _ := by ring
  have h := (convex_uIcc a auxB).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_kernelPhaseError_comp (b := b) (hγ t ht) (hslit t ht)
      (hdom t ht)).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using h

theorem limitingPhase_eq_phase {r : ℕ} (hr : 0 < r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (j : ℤ) {θ : ℝ} (hj : (r : ℝ) * θ = -2 * Real.pi * j) {s : ℂ} (hs : s ≠ 0) :
    limitingPhase r A z j s = Phase.phase r θ (saddleScale r A z) s := by
  unfold limitingPhase Phase.phase
  rw [limitingEquation_eq_phase hr hA hz j hj hs]

/-- The local holomorphic phase inherits the quantitative approximation,
with its normalization at the actual moving saddle retained. -/
theorem norm_local_phase_error {r : ℕ} {A : Fin (r - 1) → ℝ}
    {z : ℝ} {j : ℤ} {n : ℕ} {p : ℂ → ℂ} {a auxB s : ℂ} {δ ε : ℝ}
    (ha : a ∈ Metric.ball auxB δ) (hs : s ∈ Metric.ball auxB δ) (hpa : p a = 0)
    (hslit : Metric.ball auxB δ ⊆ Complex.slitPlane)
    (hmap : MapsTo (fun t : ℂ => (largeScale r n : ℂ) * t)
      (Metric.ball auxB δ) (kernelDomain r A n))
    (hp : ∀ t ∈ Metric.ball auxB δ, HasDerivAt p (-exactSaddleEquation r A z j n t) t)
    (herr : ∀ t ∈ Metric.ball auxB δ,
      ‖exactSaddleEquation r A z j n t - limitingEquation r A z j t‖ ≤ ε) :
    ‖p s + limitingPhase r A z j s - limitingPhase r A z j a‖ ≤ ‖s - a‖ * ε := by
  have he : ContinuousOn (exactSaddleEquation r A z j n) (Metric.ball auxB δ) :=
    ((differentiableOn_exactSaddleEquation r A z j n).mono (fun _ ht => hmap ht)).continuousOn
  have hl : ContinuousOn (limitingEquation r A z j) (Metric.ball auxB δ) :=
    (show DifferentiableOn ℂ (limitingEquation r A z j) (Metric.ball auxB δ) from
      fun t ht => (hasDerivAt_limitingEquation r A z j (hslit ht)).differentiableAt.differentiableWithinAt).continuousOn
  have h := Analytic.norm_primitive_sub_le_ball ha hs hp
    (fun t ht => (hasDerivAt_limitingPhase r A z j (hslit ht)).neg)
    (he.neg.sub hl.neg) (fun t ht => by
      simpa only [neg_sub_neg, norm_sub_rev] using herr t ht)
  convert h using 1
  congr 1
  simp only [Pi.neg_apply, hpa]
  ring

end ThisWork.HigherRank
