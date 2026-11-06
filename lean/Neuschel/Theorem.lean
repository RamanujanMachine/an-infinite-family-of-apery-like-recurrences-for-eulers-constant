module

public import Neuschel.ExpansionForm
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Neuschel's uniform Laplace theorem in explicit contour-parameter form. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

/-- Countably many corners, including corners accumulating only at an improper
endpoint, also give a measurable velocity. -/
theorem measurable_contour_velocity_countable {γ velocity : ℝ → ℂ} {corners : Set ℝ}
    (hcorners : corners.Countable)
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ corners → HasDerivAt γ (velocity s) s) :
    AEStronglyMeasurable velocity (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hc : ∀ᵐ s : ℝ, s ∉ corners := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hcorners.measure_zero volume
  refine (aestronglyMeasurable_deriv γ (volume.restrict (Ioo (0 : ℝ) 1))).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hc] with s hs hsc
  exact (hd s hs hsc).deriv

theorem measurable_contour_velocity {γ velocity : ℝ → ℂ} {corners : Set ℝ}
    (hcorners : corners.Finite)
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ corners → HasDerivAt γ (velocity s) s) :
    AEStronglyMeasurable velocity (volume.restrict (Ioo (0 : ℝ) 1)) :=
  measurable_contour_velocity_countable hcorners.countable hd

/-- Neuschel's Theorem 3.1 for an explicitly parameterized contour. The positive
integer `λ` is represented as `k + 1`. The final endpoint may be improper. -/
theorem neuschel_theorem_3_1 {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] [Nonempty Z] {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) {P q : ℂ → Z → ℂ}
    (hP : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {b c : ℕ → Z → ℂ}
    (hsP : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => b j z * (t - a) ^ (μ + j)) (P t z - P a z))
    (hb : ∀ z, b 0 z ≠ 0)
    (hsq : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z))
    {γ velocity : ℝ → ℂ} {v : ℂ} (hγ0 : γ 0 = a)
    (hγderiv : HasDerivWithinAt γ v (Ici 0) 0) (hv0 : v ≠ 0)
    (hγ : ContinuousOn γ (Ico 0 1)) (hγG : MapsTo γ (Ico 0 1) G)
    (hvelocity : AEStronglyMeasurable velocity (volume.restrict (Ioo 0 1)))
    {L : ℝ} (hL : 0 < L) (hv : ContinuousOn velocity (Icc 0 L))
    (hdγ : ∀ s ∈ Ioo 0 L, HasDerivAt γ (velocity s) s)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (P (γ s) z - P a z).re)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ (P (γ s) z - P a z).re)
    {N B : ℝ} (hB : 0 ≤ B)
    (hbase : ∀ z, IntegrableOn
      (fun s => Real.exp (-N * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1,
      Real.exp (-N * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) ≤ B) :
    Nonempty (UniformLaplaceExpansion μ k P q a v b c γ velocity N) := by
  obtain ⟨H, D, hD, hH, hdH, hzero, hone, hbound⟩ := uniform_laplace_expansion hG ha hμ k
    hP hdP hq hdq hsP hb hsq hγ0 hγderiv hv0 hγ hγG hvelocity hL hv hdγ hpos hend hB hbase hmass
  let A : ℕ → Z → ℂ := fun j z => phaseQuotient j 0 H 0 z * (μ : ℂ)⁻¹
  let S : ℕ → ℕ → Z → ℂ := fun m n z => ∑ j ∈ Finset.range m, A j z *
    ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
      (n : ℝ) ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)
  let R : ℕ → ℕ → Z → ℂ := fun m n z =>
    (∫ s in Ioo (0 : ℝ) 1, Complex.exp (-(n : ℂ) * (P (γ s) z - P a z)) *
      (velocity s * q (γ s) z)) - S m n z
  refine ⟨{
    absolute_convergence := ?_
    coefficient := A
    coefficient_continuous := ?_
    coefficient_zero := ?_
    coefficient_one := ?_
    remainder := R
    expansion := ?_
    remainder_bound := ?_
  }⟩
  · intro n hn z
    have hpz : ContinuousOn (fun s => P (γ s) z) (Ioo 0 1) :=
      (hdP z).continuousOn.comp (hγ.mono Ioo_subset_Ico_self)
        (fun s hs => hγG (Ioo_subset_Ico_self hs))
    have hqz : ContinuousOn (fun s => q (γ s) z) (Ioo 0 1) :=
      (hdq z).continuousOn.comp (hγ.mono Ioo_subset_Ico_self)
        (fun s hs => hγG (Ioo_subset_Ico_self hs))
    have he : ContinuousOn (fun s => Complex.exp (-(n : ℂ) * P (γ s) z)) (Ioo 0 1) :=
      (hpz.const_mul (-(n : ℂ))).cexp
    have hmeas : AEStronglyMeasurable
        (fun s => Complex.exp (-(n : ℂ) * P (γ s) z) * (velocity s * q (γ s) z))
        (volume.restrict (Ioo 0 1)) := by
      simpa only [Pi.mul_def] using
        (he.aestronglyMeasurable measurableSet_Ioo).mul
          (hvelocity.mul (hqz.aestronglyMeasurable measurableSet_Ioo))
    have hgap : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), (P a z).re ≤ (P (γ s) z).re :=
      (ae_restrict_mem measurableSet_Ioo).mono (fun s hs => by
        have h := hpos s hs z
        rw [Complex.sub_re] at h
        linarith)
    simpa only [Complex.ofReal_natCast, IntegrableOn] using
      integrable_exp_weight hn hgap (hbase z) (by simpa only [Complex.ofReal_natCast] using hmeas)
  · intro j
    have hc : Continuous (fun z => phaseQuotient j 0 H 0 z) :=
      (phaseQuotient_regular j isOpen_ball (mem_ball_self hD) hH hdH).1.comp_continuous
        (continuous_const.prodMk continuous_id) (fun z => ⟨mem_ball_self hD, mem_univ z⟩)
    exact hc.fun_mul continuous_const
  · intro z
    simp only [A, phaseQuotient, Function.iterate_zero, id_eq, hzero z,
      div_eq_mul_inv, mul_inv_rev]
    ring
  · intro z
    change phaseQuotient (0 + 1) 0 H 0 z * (μ : ℂ)⁻¹ = _
    rw [phaseQuotient_succ_center]
    change deriv (fun w => H w z) 0 * (μ : ℂ)⁻¹ = _
    rw [hone z]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro m n z
    simpa only [R, S, Complex.ofReal_natCast] using
      uncentered_residual (volume.restrict (Ioo (0 : ℝ) 1)) (n : ℝ)
        (fun s => P (γ s) z) (fun s => velocity s * q (γ s) z) (P a z) (S m n z)
  · intro m
    obtain ⟨C, hC, hbnd⟩ := hbound m
    refine ⟨C, hC, ?_⟩
    have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually hbnd
    simpa only [R, S, A, Complex.ofReal_natCast, mul_assoc] using hn

/-- The theorem for a contour with finitely many corners. The velocity is
linked to the curve on every smooth piece, and measurability is derived. -/
theorem neuschel_theorem_3_1_piecewise {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] [Nonempty Z] {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) {P q : ℂ → Z → ℂ}
    (hP : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {b c : ℕ → Z → ℂ}
    (hsP : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => b j z * (t - a) ^ (μ + j)) (P t z - P a z))
    (hb : ∀ z, b 0 z ≠ 0)
    (hsq : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z))
    {γ velocity : ℝ → ℂ} {v : ℂ} (hγ0 : γ 0 = a)
    (hγderiv : HasDerivWithinAt γ v (Ici 0) 0) (hv0 : v ≠ 0)
    (hγ : ContinuousOn γ (Ico 0 1)) (hγG : MapsTo γ (Ico 0 1) G)
    {corners : Set ℝ} (hcorners : corners.Finite)
    (hregular : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ corners → HasDerivAt γ (velocity s) s)
    {L : ℝ} (hL : 0 < L) (hv : ContinuousOn velocity (Icc 0 L))
    (hdγ : ∀ s ∈ Ioo 0 L, HasDerivAt γ (velocity s) s)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (P (γ s) z - P a z).re)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ (P (γ s) z - P a z).re)
    {N B : ℝ} (hB : 0 ≤ B)
    (hbase : ∀ z, IntegrableOn
      (fun s => Real.exp (-N * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1,
      Real.exp (-N * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) ≤ B) :
    Nonempty (UniformLaplaceExpansion μ k P q a v b c γ velocity N) := by
  exact neuschel_theorem_3_1 hG ha hμ k hP hdP hq hdq hsP hb hsq hγ0 hγderiv hv0 hγ hγG
    (measurable_contour_velocity hcorners hregular) hL hv hdγ hpos hend hB hbase hmass

/-- The same contour theorem allows countably many corners. -/
theorem neuschel_theorem_3_1_countable {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] [Nonempty Z] {G : Set ℂ} (hG : IsOpen G) {a : ℂ} (ha : a ∈ G)
    {μ : ℕ} (hμ : μ ≠ 0) (k : ℕ) {P q : ℂ → Z → ℂ}
    (hP : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    (hdP : ∀ z, DifferentiableOn ℂ (fun t => P t z) G)
    (hq : ContinuousOn (Function.uncurry q) (G ×ˢ univ))
    (hdq : ∀ z, DifferentiableOn ℂ (fun t => q t z) G) {b c : ℕ → Z → ℂ}
    (hsP : ∀ z, ∀ᶠ t in 𝓝 a,
      HasSum (fun j => b j z * (t - a) ^ (μ + j)) (P t z - P a z))
    (hb : ∀ z, b 0 z ≠ 0)
    (hsq : ∀ z, ∀ᶠ t in 𝓝 a, HasSum (fun j => c j z * (t - a) ^ (k + j)) (q t z))
    {γ velocity : ℝ → ℂ} {v : ℂ} (hγ0 : γ 0 = a)
    (hγderiv : HasDerivWithinAt γ v (Ici 0) 0) (hv0 : v ≠ 0)
    (hγ : ContinuousOn γ (Ico 0 1)) (hγG : MapsTo γ (Ico 0 1) G)
    {corners : Set ℝ} (hcorners : corners.Countable)
    (hregular : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ corners → HasDerivAt γ (velocity s) s)
    {L : ℝ} (hL : 0 < L) (hv : ContinuousOn velocity (Icc 0 L))
    (hdγ : ∀ s ∈ Ioo 0 L, HasDerivAt γ (velocity s) s)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (P (γ s) z - P a z).re)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ (P (γ s) z - P a z).re)
    {N B : ℝ} (hB : 0 ≤ B)
    (hbase : ∀ z, IntegrableOn
      (fun s => Real.exp (-N * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1,
      Real.exp (-N * (P (γ s) z).re) * ‖velocity s * q (γ s) z‖) ≤ B) :
    Nonempty (UniformLaplaceExpansion μ k P q a v b c γ velocity N) := by
  exact neuschel_theorem_3_1 hG ha hμ k hP hdP hq hdq hsP hb hsq hγ0 hγderiv hv0 hγ hγG
    (measurable_contour_velocity_countable hcorners hregular) hL hv hdγ hpos hend hB hbase hmass

end Neuschel
