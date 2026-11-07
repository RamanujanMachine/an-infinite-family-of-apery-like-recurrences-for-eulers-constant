module

public import ThisWork.Argument
public import ThisWork.CompactSaddles

/-! Canonical centered primitives and the local phase family at the exact saddles. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric MeasureTheory
open scoped Topology OnePoint

theorem hasDerivAt_segmentIntegral_ball {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball 0 r)) {s : ℂ} (hs : s ∈ ball 0 r) :
    HasDerivAt (fun t => Neuschel.segmentIntegral F 0 t) (F s) s := by
  obtain ⟨g, hg0, hg⟩ := hF.isExactOn_ball.with_val_at 0 0
  have he : (fun t => Neuschel.segmentIntegral F 0 t) =ᶠ[𝓝 s] g :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hs) (fun t ht => by
      simpa only [Set.mem_ofPred_eq, hg0, sub_zero] using
        Neuschel.segmentIntegral_eq_primitive_sub (convex_ball 0 r) hg hF.continuousOn (mem_ball_self hr) ht)
  exact (hg s hs).congr_of_eventuallyEq he

theorem continuousOn_segmentIntegral_family {Z : Type*} [TopologicalSpace Z]
    {Q : ℂ → Z → ℂ} {r : ℝ}
    (hQ : ContinuousOn (Function.uncurry Q) (ball 0 r ×ˢ univ)) :
    ContinuousOn (Function.uncurry (fun t z => Neuschel.segmentIntegral (fun u => Q u z) 0 t))
      (ball 0 r ×ˢ univ) := by
  let T := (ball (0 : ℂ) r) × Z
  let clamp (u : ℝ) := max 0 (min 1 u)
  have hclamp (u : ℝ) : 0 ≤ clamp u ∧ clamp u ≤ 1 :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hmap (w : T × ℝ) : (((clamp w.2 : ℝ) : ℂ) * w.1.1.val, w.1.2) ∈
      ball (0 : ℂ) r ×ˢ univ := by
    refine ⟨?_, mem_univ _⟩
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_of_nonneg (hclamp w.2).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hclamp w.2).2).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using w.1.1.property)
  have hc : Continuous (fun w : T × ℝ => Q (((clamp w.2 : ℝ) : ℂ) * w.1.1.val) w.1.2) :=
    hQ.comp_continuous (by dsimp only [T, clamp]; fun_prop) hmap
  have hi : Continuous (fun x : T => ∫ u : ℝ in 0..1,
      x.1.val * Q (((clamp u : ℝ) : ℂ) * x.1.val) x.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul hc) 0 1
  rw [continuousOn_iff_continuous_domRestrict]
  have hin : Continuous (fun w : (ball (0 : ℂ) r ×ˢ (univ : Set Z)) =>
      ((⟨w.val.1, w.property.1⟩ : ball (0 : ℂ) r), w.val.2)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (continuous_snd.comp continuous_subtype_val)
  convert hi.comp hin using 1
  funext w
  change (∫ u : ℝ in 0..1, (w.val.1 - 0) * Q (AffineMap.lineMap 0 w.val.1 u) w.val.2) = _
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : 0 ≤ u ∧ u ≤ 1 := by simpa only [uIcc_of_le zero_le_one, mem_Icc] using hu
  simp only [clamp, min_eq_right hu'.2, max_eq_right hu'.1, AffineMap.lineMap_apply_module,
    smul_zero, zero_add, sub_zero, Complex.real_smul]

theorem eq_neg_segmentIntegral_of_derivative {p Q : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hQ : DifferentiableOn ℂ Q (ball 0 r)) (hp0 : p 0 = 0)
    (hp : ∀ t ∈ ball 0 r, HasDerivAt p (-Q t) t) :
    EqOn p (fun t => -Neuschel.segmentIntegral Q 0 t) (ball 0 r) := by
  apply isOpen_ball.eqOn_of_deriv_eq (convex_ball 0 r).isPreconnected
    (fun t ht => (hp t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hasDerivAt_segmentIntegral_ball hr hQ ht).neg.differentiableAt.differentiableWithinAt)
    (fun t ht => (hp t ht).deriv.trans ((hasDerivAt_segmentIntegral_ball hr hQ ht).neg.deriv).symm)
    (mem_ball_self hr)
  simp only [hp0, Neuschel.segmentIntegral, sub_self, zero_mul, intervalIntegral.integral_zero,
    Pi.neg_apply, neg_zero]

namespace CompactSaddleFamily

noncomputable def phase [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} (S : CompactSaddleFamily α₁ α₂ j)
    (t : ℂ) (z : OnePoint ℕ) : ℂ :=
  -Neuschel.segmentIntegral (fun u => S.shiftedEquation u z) 0 t

theorem continuous_phase [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) :
    ContinuousOn (Function.uncurry S.phase) (ball 0 (saddleScale α₁ α₂ / 16) ×ˢ univ) := by
  exact (continuousOn_segmentIntegral_family S.continuous_shiftedEquation).neg

theorem hasDerivAt_phase [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) {t : ℂ}
    (ht : t ∈ ball 0 (saddleScale α₁ α₂ / 16)) (z : OnePoint ℕ) :
    HasDerivAt (fun u => S.phase u z) (-S.shiftedEquation t z) t := by
  exact (hasDerivAt_segmentIntegral_ball (div_pos (saddleScale_pos h₁ h₂) (by norm_num))
    (S.differentiableOn_shiftedEquation z) ht).neg

@[simp] theorem phase_zero [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) : S.phase 0 z = 0 := by
  simp only [phase, Neuschel.segmentIntegral, sub_self, zero_mul, intervalIntegral.integral_zero, neg_zero]

theorem differentiableOn_phase [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    DifferentiableOn ℂ (fun t => S.phase t z) (ball 0 (saddleScale α₁ α₂ / 16)) :=
  fun _ ht => (S.hasDerivAt_phase h₁ h₂ ht z).differentiableAt.differentiableWithinAt

theorem phase_simple_saddle [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    deriv (fun t => S.phase t z) 0 = 0 ∧ deriv (deriv (fun t => S.phase t z)) 0 ≠ 0 :=
  ThisWork.Analytic.phase_simple_saddle (mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))
    (fun _ ht => S.hasDerivAt_phase h₁ h₂ ht z) (S.shiftedEquation_zero z) (S.shiftedEquation_simple z)

theorem phase_limit [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) {t : ℂ} (ht : t ∈ ball 0 (saddleScale α₁ α₂ / 16)) :
    S.phase t ∞ = limitingPhase j (saddleScale α₁ α₂) ((saddleScale α₁ α₂ : ℂ) * rho j) -
      limitingPhase j (saddleScale α₁ α₂) (t + (saddleScale α₁ α₂ : ℂ) * rho j) := by
  have hc := saddleScale_pos h₁ h₂
  have hd : ∀ u ∈ ball 0 (saddleScale α₁ α₂ / 16),
      HasDerivAt (fun v => limitingPhase j (saddleScale α₁ α₂) (v + (saddleScale α₁ α₂ : ℂ) * rho j))
        (S.shiftedEquation u ∞) u := by
    intro u hu
    have hmem : u + (saddleScale α₁ α₂ : ℂ) * rho j ∈ saddleDisk (saddleScale α₁ α₂) j := by
      exact closedBall_subset_closedBall (by linarith : saddleScale α₁ α₂ / 8 ≤ saddleScale α₁ α₂ / 4)
        (ball_subset_closedBall (by simpa only [S.saddle_limit] using S.shifted_mem hu ∞))
    simpa only [S.shiftedEquation_limit, Function.comp_def, id_eq, mul_one] using
      (hasDerivAt_limitingPhase j hc
        ((div_pos_real_mem_slitPlane_iff hc _).mpr (saddleDisk_mem_slitPlane hc j hmem))).comp u
          ((hasDerivAt_id u).add_const ((saddleScale α₁ α₂ : ℂ) * rho j))
  have he := Neuschel.segmentIntegral_eq_primitive_sub (convex_ball 0 (saddleScale α₁ α₂ / 16)) hd
    (S.differentiableOn_shiftedEquation ∞).continuousOn
    (mem_ball_self (div_pos hc (by norm_num))) ht
  simpa only [phase, zero_add, neg_sub] using congrArg Neg.neg he

theorem eventually_kernel_eq_phase [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) :
    ∀ᶠ m : ℕ in atTop, ∀ t ∈ ball 0 (saddleScale α₁ α₂ / 16),
      normalizedKernel α₁ α₂ j (m + S.firstIndex)
        ((largeScale (m + S.firstIndex) : ℂ) * (t + S.saddle m)) =
      normalizedKernel α₁ α₂ j (m + S.firstIndex)
        ((largeScale (m + S.firstIndex) : ℂ) * S.saddle m) *
      Complex.exp (-(largeScale (m + S.firstIndex) : ℂ) * S.phase t m) := by
  have hc := saddleScale_pos h₁ h₂
  filter_upwards [(tendsto_add_atTop_nat S.firstIndex).eventually
    (eventually_saddleDisk_mapsTo_kernelDomain h₁ h₂ j)] with m hm
  have ha : S.saddle m ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4) :=
    ball_subset_ball (by linarith : saddleScale α₁ α₂ / 16 ≤ saddleScale α₁ α₂ / 4) (S.saddle_mem m)
  obtain ⟨p, hp0, hp, hk⟩ := exists_scaled_kernel_phase j hm.1 ha
    (fun _ hs => hm.2 (ball_subset_closedBall hs))
  have hmap : ∀ t ∈ ball 0 (saddleScale α₁ α₂ / 16),
      t + S.saddle m ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 4) :=
    fun _ ht => ball_subset_ball (by linarith : saddleScale α₁ α₂ / 8 ≤ saddleScale α₁ α₂ / 4)
      (S.shifted_mem ht m)
  have hcomp : ∀ t ∈ ball 0 (saddleScale α₁ α₂ / 16),
      HasDerivAt (fun u => p (u + S.saddle m)) (-S.shiftedEquation t m) t := by
    intro t ht
    simpa only [shiftedEquation, parameterEquation, sequenceFamily_nat, Function.comp_def, id_eq, mul_one] using
      (hp _ (hmap t ht)).comp t ((hasDerivAt_id t).add_const (S.saddle m))
  have he := eq_neg_segmentIntegral_of_derivative (div_pos hc (by norm_num))
    (S.differentiableOn_shiftedEquation m) (by simpa only [zero_add] using hp0) hcomp
  intro t ht
  simpa only [phase, he ht] using hk _ (hmap t ht)

end CompactSaddleFamily

end ThisWork.Analytic
