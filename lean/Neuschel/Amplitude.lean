module

public import Neuschel.LocalPhase

/-! The amplitude after the uniform holomorphic change of variable. -/

@[expose] public section

namespace Neuschel

open Set Filter Metric
open scoped Topology

variable {Z : Type*} [TopologicalSpace Z]
variable {p : ℂ → Z → ℂ} {a : ℂ} {G : Set ℂ}

namespace LocalInverseFamily

variable (e : LocalInverseFamily p a G)

theorem differentiableOn_sourceBall :
    ∀ z, DifferentiableOn ℂ (fun t => p t z) (ball a e.sourceRadius) :=
  fun z t ht => (differentiableAt_of_deriv_ne_zero (e.deriv_ne_zero t ht z)).differentiableWithinAt

theorem hasDerivAt_inverse_on_source
    (hd : ∀ z, DifferentiableOn ℂ (fun t => p t z) (ball a e.sourceRadius))
    {w : ℂ} (hw : w ∈ ball 0 e.targetRadius) (z : Z) :
    HasDerivAt (fun u => e.inverse u z) (deriv (fun t => p t z) (e.inverse w z))⁻¹ w :=
  ({ e with source_subset := Subset.rfl } : LocalInverseFamily p a (ball a e.sourceRadius))
    |>.hasDerivAt_inverse isOpen_ball hd hw z

theorem inverse_center (hz : ∀ z, p a z = 0) (z : Z) : e.inverse 0 z = a := by
  simpa only [hz z] using e.left_inv z a (mem_ball_self e.sourceRadius_pos)
    (show p a z ∈ ball 0 e.targetRadius from (hz z).symm ▸ mem_ball_self e.targetRadius_pos)

theorem deriv_inverse_center (hz : ∀ z, p a z = 0) {β : Z → ℂ}
    (hd : ∀ z, HasDerivAt (fun t => p t z) (β z) a) (hne : ∀ z, β z ≠ 0) (z : Z) :
    deriv (fun u => e.inverse u z) 0 = (β z)⁻¹ := by
  have hp : HasDerivAt (fun t => p t z) (β z) (e.inverse 0 z) :=
    (e.inverse_center hz z).symm ▸ hd z
  exact (HasDerivAt.of_local_left_inverse
    ((e.differentiable_inverse z).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self e.targetRadius_pos))).continuousAt hp (hne z)
    (Filter.mem_of_superset (ball_mem_nhds 0 e.targetRadius_pos)
      (fun u hu => e.right_inv u hu z))).deriv

/-- The Jacobian is part of the transformed amplitude. -/
noncomputable def amplitude (q : ℂ → Z → ℂ) (w : ℂ) (z : Z) : ℂ :=
  q (e.inverse w z) z * deriv (fun u => e.inverse u z) w

theorem continuousOn_amplitude {q : ℂ → Z → ℂ}
    (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ)) :
    ContinuousOn (Function.uncurry (e.amplitude q)) (ball 0 e.targetRadius ×ˢ univ) :=
  (hq.comp (e.continuous_inverse.prodMk continuous_snd.continuousOn)
    (fun w hw => ⟨e.source_subset (e.inverse_mem w.1 hw.1 w.2), mem_univ w.2⟩)).mul
      e.continuous_deriv_inverse

theorem differentiableOn_amplitude {q : ℂ → Z → ℂ}
    (hq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) :
    ∀ z, DifferentiableOn ℂ (fun w => e.amplitude q w z) (ball 0 e.targetRadius) :=
  fun z => ((hq z).comp (e.differentiable_inverse z)
    (fun w hw => e.source_subset (e.inverse_mem w hw z))).mul
      ((e.differentiable_inverse z).deriv isOpen_ball)

noncomputable def amplitudeFactor (k : ℕ) (g : ℂ → Z → ℂ) (w : ℂ) (z : Z) : ℂ :=
  dslope (fun u => e.inverse u z) 0 w ^ k * e.amplitude g w z

theorem continuousOn_amplitudeFactor (k : ℕ) {g : ℂ → Z → ℂ}
    (hg : ContinuousOn (Function.uncurry g) (G ×ˢ univ)) :
    ContinuousOn (Function.uncurry (e.amplitudeFactor k g)) (ball 0 e.targetRadius ×ˢ univ) :=
  ((continuousOn_dslope_family isOpen_ball (mem_ball_self e.targetRadius_pos)
    e.continuous_inverse e.differentiable_inverse).pow k).mul (e.continuousOn_amplitude hg)

theorem differentiableOn_amplitudeFactor (k : ℕ) {g : ℂ → Z → ℂ}
    (hg : ∀ z, DifferentiableOn ℂ (fun t => g t z) G) :
    ∀ z, DifferentiableOn ℂ (fun w => e.amplitudeFactor k g w z) (ball 0 e.targetRadius) :=
  fun z => (((Complex.differentiableOn_dslope (ball_mem_nhds 0 e.targetRadius_pos)).mpr
    (e.differentiable_inverse z)).pow k).mul (e.differentiableOn_amplitude hg z)

theorem amplitude_eq_pow_mul_factor (k : ℕ) (hz : ∀ z, p a z = 0)
    {q g : ℂ → Z → ℂ} (hq : ∀ t ∈ G, ∀ z, q t z = (t - a) ^ k * g t z)
    {w : ℂ} (hw : w ∈ ball 0 e.targetRadius) (z : Z) :
    e.amplitude q w z = w ^ k * e.amplitudeFactor k g w z := by
  have hdiff : e.inverse w z - a = w * dslope (fun u => e.inverse u z) 0 w := by
    simpa only [sub_zero, smul_eq_mul, e.inverse_center hz z] using
      (sub_smul_dslope (fun u => e.inverse u z) 0 w).symm
  simp only [amplitude, hq _ (e.source_subset (e.inverse_mem w hw z)), hdiff,
    mul_pow, amplitudeFactor, mul_assoc]

theorem amplitudeFactor_center (k : ℕ) (g : ℂ → Z → ℂ) (hz : ∀ z, p a z = 0) (z : Z) :
    e.amplitudeFactor k g 0 z = g a z * deriv (fun u => e.inverse u z) 0 ^ (k + 1) := by
  simp only [amplitudeFactor, dslope_same, amplitude, e.inverse_center hz z, pow_succ]
  ring

theorem amplitudeFactor_center_of_hasDerivAt (k : ℕ) (g : ℂ → Z → ℂ)
    (hz : ∀ z, p a z = 0) {β : Z → ℂ}
    (hd : ∀ z, HasDerivAt (fun t => p t z) (β z) a) (hne : ∀ z, β z ≠ 0) (z : Z) :
    e.amplitudeFactor k g 0 z = g a z / β z ^ (k + 1) := by
  rw [e.amplitudeFactor_center k g hz z, e.deriv_inverse_center hz hd hne z,
    inv_pow, div_eq_mul_inv]

/-- The transformed amplitude has exactly the expected vanishing factor, with
a jointly continuous holomorphic remainder and an explicit leading value. -/
theorem exists_amplitude_factor_from_expansion (k : ℕ) (hG : IsOpen G) (ha : a ∈ G)
    (hz : ∀ z, p a z = 0) {q : ℂ → Z → ℂ}
    (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hd : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {c : ℕ → Z → ℂ}
    (hs : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun n => c n z * (t - a) ^ (k + n)) (q t z)) :
    ∃ H : ℂ → Z → ℂ, ContinuousOn (Function.uncurry H) (ball 0 e.targetRadius ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun w => H w z) (ball 0 e.targetRadius)) ∧
      (∀ w ∈ ball 0 e.targetRadius, ∀ z, e.amplitude q w z = w ^ k * H w z) ∧
      (∀ z, H 0 z = c 0 z * deriv (fun u => e.inverse u z) 0 ^ (k + 1)) ∧
      H = e.amplitudeFactor k (phaseQuotient k a q) := by
  have hg := phaseQuotient_regular k hG ha hq hd
  exact ⟨e.amplitudeFactor k (phaseQuotient k a q), e.continuousOn_amplitudeFactor k hg.1,
    e.differentiableOn_amplitudeFactor k hg.2,
    fun w hw z => e.amplitude_eq_pow_mul_factor k hz
      (fun t _ z => eq_pow_mul_phaseQuotient_of_expansion k (hs z) t) hw z,
    ⟨fun z => (e.amplitudeFactor_center k _ hz z).trans
      (congrArg (fun u : ℂ => u * deriv (fun u => e.inverse u z) 0 ^ (k + 1))
        (phaseQuotient_center_of_expansion k (hs z))), rfl⟩⟩

end LocalInverseFamily

end Neuschel
