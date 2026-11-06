module

public import Neuschel.LocalExpansion
public import Neuschel.PhaseGap
public import Neuschel.TailEstimate

/-! Splitting a possibly improper contour integral into its local part and tail. -/

public section

namespace Neuschel

open Set Filter Metric MeasureTheory
open scoped Topology

/-- Splitting at an interior cutoff also applies to an improper endpoint at 1.
Absolute integrability is expressed by the restricted Lebesgue integral. -/
theorem contour_integral_split {f : ℝ → ℂ} {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hf : IntegrableOn f (Ioo 0 1)) :
    (∫ s in Ioo (0 : ℝ) 1, f s) = (∫ s in 0..δ, f s) + ∫ s in Ioo δ 1, f s := by
  rw [intervalIntegral.integral_of_le hδ.1.le, ← Ioc_union_Ioo_eq_Ioo hδ.1.le hδ.2,
    Measure.restrict_union (show Disjoint (Ioc (0 : ℝ) δ) (Ioo δ 1) from
      disjoint_left.mpr (fun _ hs ht => (not_lt_of_ge hs.2) ht.1)) measurableSet_Ioo]
  exact integral_add_measure
    (hf.mono_set (fun _ hs => ⟨hs.1, hs.2.trans_lt hδ.2⟩))
    (hf.mono_set (fun _ hs => ⟨hδ.1.trans hs.1, hs.2⟩))

/-- The actual nonlocal contour tail is uniformly exponentially small.
Its phase gap is derived from positivity and the endpoint hypothesis. -/
theorem uniform_contour_tail {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
    {p q : ℝ → Z → ℂ} {N B : ℝ}
    (hp : ContinuousOn (Function.uncurry p) (Ioo 0 1 ×ˢ univ))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (p s z).re)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ (p s z).re)
    (hbase : ∀ z, IntegrableOn (fun s => Real.exp (-N * (p s z).re) * ‖q s z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1, Real.exp (-N * (p s z).re) * ‖q s z‖) ≤ B)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    ∃ ε > 0, ∀ n : ℝ, N ≤ n → ∀ z,
      ‖∫ s in Ioo δ 1, Complex.exp (-(n : ℂ) * p s z) * q s z‖ ≤
        B * Real.exp (-(n - N) * ε) := by
  obtain ⟨ε, hε, hgap⟩ := uniform_gap_on_tail (f := fun s z => (p s z).re)
    (by simpa only [Function.comp_def, Function.uncurry_def] using Complex.continuous_re.comp_continuousOn hp) hpos hend hδ
  refine ⟨ε, hε, fun n hn z => ?_⟩
  have hsub : Ioo δ 1 ⊆ Ioo (0 : ℝ) 1 := fun s hs => ⟨hδ.1.trans hs.1, hs.2⟩
  have hmassTail : (∫ s in Ioo δ 1, Real.exp (-N * (p s z).re) * ‖q s z‖) ≤ B :=
    (setIntegral_mono_set (hbase z)
      (Eventually.of_forall (fun s => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)))
      (Eventually.of_forall hsub)).trans (hmass z)
  have hbound := norm_integral_exp_weight_le hn
    ((ae_restrict_mem measurableSet_Ioo).mono (fun s hs => hgap s ⟨hs.1.le, hs.2⟩ z))
    ((hbase z).mono_set hsub)
  exact hbound.trans ((mul_le_mul_of_nonneg_left hmassTail (Real.exp_nonneg _)).trans_eq (mul_comm _ _))

/-- A local asymptotic expansion extends to the full contour when the original
base integral is uniformly bounded and the endpoint phase has a positive gap. -/
theorem uniform_contour_expansion_from_local {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] [Nonempty Z] {p q : ℝ → Z → ℂ} {N B b : ℝ} (hB : 0 ≤ B)
    (hp : ContinuousOn (Function.uncurry p) (Ioo 0 1 ×ˢ univ))
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ z, 0 < (p s z).re)
    (hend : ∃ r < (1 : ℝ), ∃ ε > 0, ∀ s ∈ Ioo r 1, ∀ z, ε ≤ (p s z).re)
    (hbase : ∀ z, IntegrableOn (fun s => Real.exp (-N * (p s z).re) * ‖q s z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1, Real.exp (-N * (p s z).re) * ‖q s z‖) ≤ B)
    (hmeas : ∀ n : ℝ, N ≤ n → ∀ z, AEStronglyMeasurable
      (fun s => Complex.exp (-(n : ℂ) * p s z) * q s z) (volume.restrict (Ioo 0 1)))
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {S : ℝ → Z → ℂ}
    (hlocal : ∃ C ≥ 0, ∀ᶠ n : ℝ in atTop, ∀ z,
      ‖(∫ s in 0..δ, Complex.exp (-(n : ℂ) * p s z) * q s z) - S n z‖ ≤ C * n ^ b) :
    ∃ C ≥ 0, ∀ᶠ n : ℝ in atTop, ∀ z,
      ‖(∫ s in Ioo (0 : ℝ) 1, Complex.exp (-(n : ℂ) * p s z) * q s z) - S n z‖ ≤ C * n ^ b := by
  obtain ⟨ε, hε, htail⟩ := uniform_contour_tail hp hpos hend hbase hmass hδ
  obtain ⟨C, hC, hlocal⟩ := hlocal
  refine ⟨C + B * Real.exp (N * ε), add_nonneg hC (mul_nonneg hB (Real.exp_nonneg _)), ?_⟩
  filter_upwards [hlocal, eventually_ge_atTop N, eventually_exp_shift_le_rpow hε b N]
    with n hlocal hn hexp z
  have hi : IntegrableOn (fun s => Complex.exp (-(n : ℂ) * p s z) * q s z) (Ioo 0 1) :=
    integrable_exp_weight (ε := 0) hn
      ((ae_restrict_mem measurableSet_Ioo).mono (fun s hs => (hpos s hs z).le))
      (hbase z) (hmeas n hn z)
  rw [contour_integral_split hδ hi]
  have ht := (htail n hn z).trans (mul_le_mul_of_nonneg_left hexp hB)
  have htri := (norm_add_le
    ((∫ s in 0..δ, Complex.exp (-(n : ℂ) * p s z) * q s z) - S n z)
    (∫ s in Ioo δ 1, Complex.exp (-(n : ℂ) * p s z) * q s z)).trans
    (add_le_add (hlocal z) ht)
  simpa only [sub_add_eq_add_sub, add_mul, mul_assoc] using htri

theorem centered_real_weight (N : ℝ) (P a q : ℂ) :
    Real.exp (-N * (P - a).re) * ‖q‖ =
      Real.exp (N * a.re) * (Real.exp (-N * P.re) * ‖q‖) := by
  rw [← mul_assoc, ← Real.exp_add, Complex.sub_re]
  congr 2
  ring

/-- Centering the phase preserves a uniform base absolute-integral bound,
since the saddle values vary continuously over a compact parameter space. -/
theorem exists_centered_base_bound {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    {p q : ℝ → Z → ℂ} {a : Z → ℂ} (ha : Continuous a) {N B : ℝ} (hB : 0 ≤ B)
    (hbase : ∀ z, IntegrableOn (fun s => Real.exp (-N * (p s z).re) * ‖q s z‖) (Ioo 0 1))
    (hmass : ∀ z, (∫ s in Ioo (0 : ℝ) 1, Real.exp (-N * (p s z).re) * ‖q s z‖) ≤ B) :
    ∃ C ≥ 0,
      (∀ z, IntegrableOn (fun s => Real.exp (-N * (p s z - a z).re) * ‖q s z‖) (Ioo 0 1)) ∧
      ∀ z, (∫ s in Ioo (0 : ℝ) 1, Real.exp (-N * (p s z - a z).re) * ‖q s z‖) ≤ C := by
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn
    (((Complex.continuous_re.comp ha).const_mul N).rexp.continuousOn)
  refine ⟨max K 0 * B, mul_nonneg (le_max_right _ _) hB, ?_, ?_⟩
  · intro z
    simpa only [IntegrableOn, centered_real_weight] using (hbase z).const_mul (Real.exp (N * (a z).re))
  · intro z
    rw [show (fun s => Real.exp (-N * (p s z - a z).re) * ‖q s z‖) =
      (fun s => Real.exp (N * (a z).re) * (Real.exp (-N * (p s z).re) * ‖q s z‖)) from
        funext (fun s => centered_real_weight N (p s z) (a z) (q s z)), integral_const_mul]
    have hzK : |Real.exp (N * (a z).re)| ≤ K := by
      simpa only [Real.norm_eq_abs, Function.comp_def] using hK z (mem_univ z)
    have hz : Real.exp (N * (a z).re) ≤ max K 0 :=
      (le_abs_self _).trans (hzK.trans (le_max_left _ _))
    exact mul_le_mul hz (hmass z) (integral_nonneg (fun s => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))) (le_max_right _ _)

end Neuschel
