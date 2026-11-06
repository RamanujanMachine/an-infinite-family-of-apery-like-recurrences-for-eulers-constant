module

public import Neuschel.GlobalContour
public import Neuschel.Coefficients

/-! Uniform Laplace expansion on a parameterized contour with an improper endpoint. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

theorem continuousOn_contour_family {Z : Type*} [TopologicalSpace Z]
    {G : Set ℂ} {P : ℂ → Z → ℂ}
    (hP : ContinuousOn (Function.uncurry P) (G ×ˢ univ))
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ico 0 1)) (hγG : MapsTo γ (Ico 0 1) G) :
    ContinuousOn (Function.uncurry (fun s z => P (γ s) z)) (Ioo 0 1 ×ˢ univ) := by
  simpa only [Function.comp_def, Function.uncurry_def, Prod.map_fst, Prod.map_snd, id_eq] using
    hP.comp ((hγ.mono Ioo_subset_Ico_self).prodMap (continuousOn_id (s := (univ : Set Z))))
      (fun x hx => ⟨hγG (Ioo_subset_Ico_self hx.1), hx.2⟩)

/-- Parameterized uniform Laplace expansion with a centered phase. The amplitude
has vanishing order `k`, so the paper's positive integer `λ` is `k + 1`.
Only an initial smooth piece is needed for the local change of variable; the
remaining contour enters through its measurable velocity and absolute integral. -/
theorem uniform_laplace_expansion_centered {Z : Type*} [TopologicalSpace Z]
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
      (fun s => Real.exp (-N * (P (γ s) z - P a z).re) * ‖velocity s * q (γ s) z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1,
      Real.exp (-N * (P (γ s) z - P a z).re) * ‖velocity s * q (γ s) z‖) ≤ B) :
    ∃ H : ℂ → Z → ℂ, ∃ D > 0,
      ContinuousOn (Function.uncurry H) (ball 0 D ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun w => H w z) (ball 0 D)) ∧
      (∀ z, H 0 z = c 0 z / leadingRoot μ v (b 0 z) ^ (k + 1)) ∧
      (∀ z, deriv (fun w => H w z) 0 =
        (c 1 z - ((k : ℂ) + 2) * b 1 z * c 0 z / ((μ : ℂ) * b 0 z)) /
          leadingRoot μ v (b 0 z) ^ (k + 2)) ∧
      ∀ m : ℕ, ∃ C ≥ 0, ∀ᶠ n : ℝ in atTop, ∀ z,
        ‖(∫ s in Ioo (0 : ℝ) 1,
            Complex.exp (-(n : ℂ) * (P (γ s) z - P a z)) * (velocity s * q (γ s) z)) -
          ∑ j ∈ Finset.range m, phaseQuotient j 0 H 0 z * (μ : ℂ)⁻¹ *
            ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
              n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)‖ ≤
        C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) := by
  obtain ⟨M, hML⟩ := exists_localContourModel_below hG ha hμ hP hdP hsP hb hγderiv hγ0 hv0 hpos hL
  have hγM : ContinuousOn γ (Icc 0 M.cutoff) :=
    hγ.mono (fun s hs => ⟨hs.1, hs.2.trans_lt M.cutoff_mem.2⟩)
  have hvM : ContinuousOn velocity (Icc 0 M.cutoff) :=
    hv.mono (fun s hs => ⟨hs.1, hs.2.trans hML.le⟩)
  obtain ⟨H, hH, hdH, hcenterH, hcanonical, hlocal⟩ := M.local_expansion hμ hG ha k hdP hq hdq hsq hγ0 hγM hvM
    (fun s hs => hdγ s ⟨hs.1, hs.2.trans hML⟩)
  refine ⟨H, M.inverseFamily.targetRadius, M.inverseFamily.targetRadius_pos, hH, hdH, ?_, ?_, fun m => ?_⟩
  · intro z
    rw [hcenterH z, M.deriv_inverse_center hG ha hv0 z, inv_pow, div_eq_mul_inv]
  · intro z
    rw [hcanonical]
    exact M.transformed_factor_first hG ha hμ hv0 hb hsP k hsq z
  · have hpγ := continuousOn_contour_family hP hγ hγG
    have hPa : Continuous (fun z => P a z) :=
      hP.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
    have hcenter : ContinuousOn (Function.uncurry (fun s z => P (γ s) z - P a z))
        (Ioo 0 1 ×ˢ univ) := by
      simpa only [Function.uncurry_def, Pi.sub_apply, Function.comp_def] using
        hpγ.fun_sub (hPa.comp continuous_snd).continuousOn
    refine uniform_contour_expansion_from_local hB hcenter hpos hend hbase hmass ?_ M.cutoff_mem ?_
    · intro n _ z
      have hpz : ContinuousOn (fun s => P (γ s) z) (Ioo 0 1) :=
        (hdP z).continuousOn.comp (hγ.mono Ioo_subset_Ico_self)
          (fun s hs => hγG (Ioo_subset_Ico_self hs))
      have hqz : ContinuousOn (fun s => q (γ s) z) (Ioo 0 1) :=
        (hdq z).continuousOn.comp (hγ.mono Ioo_subset_Ico_self)
          (fun s hs => hγG (Ioo_subset_Ico_self hs))
      have he : ContinuousOn (fun s => Complex.exp (-(n : ℂ) * (P (γ s) z - P a z))) (Ioo 0 1) :=
        ((hpz.fun_sub continuousOn_const).const_mul (-(n : ℂ))).cexp
      simpa only [Pi.mul_def] using
        (he.aestronglyMeasurable measurableSet_Ioo).mul
          (hvelocity.mul (hqz.aestronglyMeasurable measurableSet_Ioo))
    · simpa only [mul_left_comm (velocity _) (Complex.exp _) (q _ _)] using hlocal m
/-- The full parameterized all-orders uniform expansion, using the original
uncentered absolute-integral hypothesis. The displayed integral is normalized by
the saddle exponential. This theorem also allows real Laplace parameters. -/
theorem uniform_laplace_expansion {Z : Type*} [TopologicalSpace Z]
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
    ∃ H : ℂ → Z → ℂ, ∃ D > 0,
      ContinuousOn (Function.uncurry H) (ball 0 D ×ˢ univ) ∧
      (∀ z, DifferentiableOn ℂ (fun w => H w z) (ball 0 D)) ∧
      (∀ z, H 0 z = c 0 z / leadingRoot μ v (b 0 z) ^ (k + 1)) ∧
      (∀ z, deriv (fun w => H w z) 0 =
        (c 1 z - ((k : ℂ) + 2) * b 1 z * c 0 z / ((μ : ℂ) * b 0 z)) /
          leadingRoot μ v (b 0 z) ^ (k + 2)) ∧
      ∀ m : ℕ, ∃ C ≥ 0, ∀ᶠ n : ℝ in atTop, ∀ z,
        ‖(∫ s in Ioo (0 : ℝ) 1,
            Complex.exp (-(n : ℂ) * (P (γ s) z - P a z)) * (velocity s * q (γ s) z)) -
          ∑ j ∈ Finset.range m, phaseQuotient j 0 H 0 z * (μ : ℂ)⁻¹ *
            ((Real.Gamma ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) /
              n ^ ((((j + k : ℕ) : ℝ) + 1) / (μ : ℝ)) : ℝ) : ℂ)‖ ≤
        C * n ^ (-((((m + k : ℕ) : ℝ) + 1) / (μ : ℝ))) := by
  have hPa : Continuous (fun z => P a z) :=
    hP.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨ha, mem_univ z⟩)
  obtain ⟨B', hB', hbase', hmass'⟩ := exists_centered_base_bound hPa hB hbase hmass
  exact uniform_laplace_expansion_centered hG ha hμ k hP hdP hq hdq hsP hb hsq
    hγ0 hγderiv hv0 hγ hγG hvelocity hL hv hdγ hpos hend hB' hbase' hmass'

end Neuschel
