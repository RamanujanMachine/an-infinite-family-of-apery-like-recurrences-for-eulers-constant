module

public import ThisWork.ParabolicKernelApproximation

/-! Uniform limiting-phase gaps on translated parabolic arcs. -/

@[expose] public section
namespace ThisWork

open Set Metric Filter
open scoped Topology

theorem exists_uniform_parabolic_phase_translation {a c ε : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hε : 0 < ε) (r : ℕ) (θ B : ℝ) :
    ∃ d > 0, ∀ δ : ℂ, ‖δ‖ < d → ∀ auxB ∈ Icc (-B) B,
      ‖Phase.phase r θ c (δ + parabolicPoint a auxB) - Phase.phase r θ c (parabolicPoint a auxB)‖ < ε := by
  let T := Icc (-B) B
  have hφ : ContinuousOn (Phase.phase r θ c) Complex.slitPlane :=
    (show DifferentiableOn ℂ (Phase.phase r θ c) Complex.slitPlane from fun s hs =>
      (Phase.hasDerivAt_phase r θ hc ((ThisWork.div_pos_real_mem_slitPlane_iff hc s).mpr hs)).differentiableAt.differentiableWithinAt).continuousOn
  let p : ℂ → T → ℂ := fun δ auxB =>
    Phase.phase r θ c (δ + parabolicPoint a auxB.val) - Phase.phase r θ c (parabolicPoint a auxB.val)
  have hg : Continuous (fun w : ℂ × T => w.1 + parabolicPoint a w.2.val) := by
    unfold parabolicPoint
    fun_prop
  have hb : Continuous (fun w : ℂ × T => parabolicPoint a w.2.val) := by
    unfold parabolicPoint
    fun_prop
  have hp : ContinuousOn (Function.uncurry p) (ball (0 : ℂ) (a ^ 2 / 8) ×ˢ univ) := by
    apply (hφ.comp hg.continuousOn _).sub (hφ.comp hb.continuousOn _)
    · intro w hw
      have hn : ‖w.1‖ ≤ a ^ 2 / 8 := by
        exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw.1)
      exact region_mem_slitPlane (by positivity : 0 < a ^ 2 / 4)
        (by positivity : 0 < a ^ 2 / 4) (translated_parabola_region ha hn w.2.val)
    · intro w _
      exact parabolicPoint_mem_slitPlane ha w.2.val
  obtain ⟨d, hd, _, hmap⟩ := Neuschel.exists_uniform_mapsTo_nhds isOpen_ball
    (mem_ball_self (by positivity : 0 < a ^ 2 / 8)) hp (V := ball 0 ε) isOpen_ball
    (fun auxB => by simpa only [p, zero_add, sub_self] using mem_ball_self hε)
  refine ⟨d, hd, fun δ hδ auxB hb => ?_⟩
  have h := hmap ⟨auxB, hb⟩ (show δ ∈ ball 0 d by simpa only [mem_ball, dist_zero_right] using hδ)
  simpa only [mem_ball, dist_zero_right, p] using h

theorem exists_translated_parabolic_phase_gap {r : ℕ} (hr : 0 < r)
    {a b₀ B h : ℝ} (ha : 0 < a) (hb₀ : |b₀| ≤ B) (hh : 0 < h) :
    ∃ d > 0, ∃ ε > 0, ∀ δ : ℂ, ‖δ‖ < d → ∀ auxB ∈ Icc (-B) B,
      h ≤ |auxB - b₀| →
        ε ≤ (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2)
          (δ + parabolicPoint a b₀)).re -
          (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2)
            (δ + parabolicPoint a auxB)).re := by
  obtain ⟨g, hg, hgap⟩ := exists_parabolicPhase_compact_gap ha hh b₀ B
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  obtain ⟨d, hd, htrans⟩ := exists_uniform_parabolic_phase_translation ha
    (by positivity : 0 < a ^ 2 + b₀ ^ 2) (by positivity : 0 < (r : ℝ) * g / 4)
    r (2 * Real.arctan (b₀ / a)) B
  refine ⟨d, hd, (r : ℝ) * g / 2, by positivity, ?_⟩
  intro δ hδ auxB hb hbd
  have h0 := (Complex.abs_re_le_norm _).trans_lt (htrans δ hδ b₀ (abs_le.mp hb₀))
  have h1 := (Complex.abs_re_le_norm _).trans_lt (htrans δ hδ auxB hb)
  rw [Complex.sub_re] at h0 h1
  have hs : (r : ℝ) * g ≤
      (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2) (parabolicPoint a b₀)).re -
        (Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2) (parabolicPoint a auxB)).re := by
    rw [phase_re_parabolicPoint r ha b₀ b₀, phase_re_parabolicPoint r ha b₀ auxB]
    nlinarith [hgap auxB hb hbd]
  linarith [(abs_lt.mp h0).1, (abs_lt.mp h1).2]

/-- The actual Gamma kernel has a uniform logarithmic gap on every bounded
translated parabolic arc outside a fixed saddle window. -/
theorem uniform_log_kernel_parabolic_gap {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (j : ℤ) {a b₀ B h : ℝ} (ha : 0 < a) (hb₀ : |b₀| ≤ B) (hh : 0 < h)
    (hscale : saddleScale r A z = a ^ 2 + b₀ ^ 2)
    (hj : (r : ℝ) * (2 * Real.arctan (b₀ / a)) = -2 * Real.pi * j) :
    ∃ d > 0, ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ < d →
      ∀ auxB ∈ Icc (-B) B, h ≤ |auxB - b₀| →
        ε * largeScale r n ≤
          Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a b₀))‖ -
            Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB))‖ := by
  obtain ⟨d, hd, ε, hε, hgap⟩ := exists_translated_parabolic_phase_gap
    (by omega : 0 < r) ha hb₀ hh
  have hB : 0 ≤ B := (abs_nonneg b₀).trans hb₀
  obtain ⟨C, hC, herr⟩ := uniform_kernelPhaseError_parabola hr hA b z j ha hB
  have ht : Tendsto (fun n => C * smallParameter r n * (2 * B)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((smallParameter_tendsto (show 0 < r by omega)).const_mul C).mul_const (2 * B)
  refine ⟨min d (a ^ 2 / 8), lt_min hd (by positivity), ε / 2, half_pos hε, ?_⟩
  filter_upwards [herr, ht.eventually_le_const (half_pos hε), eventually_gt_atTop (0 : ℕ)]
    with n hn hsmall hn0 δ hδ auxB hb hbd
  have hδd := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδa : ‖δ‖ ≤ a ^ 2 / 8 := le_of_lt (lt_of_lt_of_le hδ (min_le_right _ _))
  have hslit (t : ℝ) : δ + parabolicPoint a t ∈ Complex.slitPlane :=
    region_mem_slitPlane (by positivity : 0 < a ^ 2 / 4)
      (by positivity : 0 < a ^ 2 / 4) (translated_parabola_region ha hδa t)
  have hphase (t : ℝ) : limitingPhase r A z j (δ + parabolicPoint a t) =
      Phase.phase r (2 * Real.arctan (b₀ / a)) (a ^ 2 + b₀ ^ 2) (δ + parabolicPoint a t) := by
    rw [limitingPhase_eq_phase (by omega : 0 < r) hA hz j hj
      (Complex.slitPlane_ne_zero (hslit t)), hscale]
  have he := hn δ hδa b₀ auxB hb₀ (abs_le.mpr hb)
  dsimp only [kernelPhaseError] at he
  rw [hphase b₀, hphase auxB] at he
  have hdist : |auxB - b₀| ≤ 2 * B := (abs_sub auxB b₀).trans (by linarith [(abs_le.mpr hb)])
  have hR : 0 < largeScale r n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hs : 0 ≤ smallParameter r n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have heB := mul_le_mul_of_nonneg_left hdist (mul_nonneg (mul_nonneg hR.le hC) hs)
  have hsmallR := mul_le_mul_of_nonneg_left hsmall hR.le
  have hgapR := mul_le_mul_of_nonneg_left (hgap δ hδd auxB hb hbd) hR.le
  nlinarith [(abs_le.mp he).2]

theorem uniform_kernel_parabolic_gap {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (j : ℤ) {a b₀ B h : ℝ} (ha : 0 < a) (hb₀ : |b₀| ≤ B) (hh : 0 < h)
    (hscale : saddleScale r A z = a ^ 2 + b₀ ^ 2)
    (hj : (r : ℝ) * (2 * Real.arctan (b₀ / a)) = -2 * Real.pi * j) :
    ∃ d > 0, ∃ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ δ : ℂ, ‖δ‖ < d →
      ∀ auxB ∈ Icc (-B) B, h ≤ |auxB - b₀| →
        ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB))‖ ≤
          ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a b₀))‖ *
            Real.exp (-ε * largeScale r n) := by
  obtain ⟨d, hd, ε, hε, hgap⟩ := uniform_log_kernel_parabolic_gap hr hA hz b j ha hb₀ hh hscale hj
  refine ⟨min d (a ^ 2 / 8), lt_min hd (by positivity), ε, hε, ?_⟩
  filter_upwards [hgap, eventually_translated_parabola_in_kernelDomain (by omega : 0 < r) hA ha]
    with n hn hdom δ hδ auxB hb hbd
  have hg := hn δ (lt_of_lt_of_le hδ (min_le_left _ _)) auxB hb hbd
  have hδa : ‖δ‖ ≤ a ^ 2 / 8 := le_of_lt (lt_of_lt_of_le hδ (min_le_right _ _))
  have hnz := kernel_ne_zero b z j n (hdom δ hδa b₀)
  calc
    _ ≤ Real.exp (Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a auxB))‖) :=
      Real.le_exp_log _
    _ ≤ Real.exp (Real.log ‖kernel r b A z j n ((largeScale r n : ℂ) * (δ + parabolicPoint a b₀))‖ +
        (-ε * largeScale r n)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr hnz)]

end ThisWork
