module

public import ThisWork.CompactEquation

/-! A compact continuous family of actual arbitrary-rank saddles and its
limiting saddle. Existence is proved from the Gamma-kernel estimates. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric
open scoped Topology OnePoint

noncomputable def parameterEquation (r : ℕ) (A : Fin (r - 1) → ℝ)
    (z : ℝ) (j : ℤ) (N : ℕ) : ℂ → OnePoint ℕ → ℂ :=
  Analytic.sequenceFamily (fun b => exactSaddleEquation r A z j (b + N)) (limitingEquation r A z j)

structure CompactSaddleFamily (r : ℕ) (A : Fin (r - 1) → ℝ) (z : ℝ) (j : ℤ)
    (ζ : ℂ) (δ : ℝ) where
  firstIndex : ℕ
  saddle : C(OnePoint ℕ, ℂ)
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  saddle_limit : saddle ∞ = ζ
  saddle_mem : ∀ q, saddle q ∈ ball ζ (δ / 4)
  equation_zero : ∀ q, parameterEquation r A z j firstIndex (saddle q) q = 0
  equation_simple : ∀ q, deriv (fun s => parameterEquation r A z j firstIndex s q) (saddle q) ≠ 0
  displacement : ∀ b : ℕ, ‖saddle b - ζ‖ ≤ errorConstant * smallParameter r (b + firstIndex)
  continuous_equation : ContinuousOn (Function.uncurry (parameterEquation r A z j firstIndex))
    (ball ζ δ ×ˢ univ)
  holomorphic_equation : ∀ q, DifferentiableOn ℂ (fun s => parameterEquation r A z j firstIndex s q) (ball ζ δ)

theorem exists_compactSaddleFamily {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} (hA : ∀ i, 0 < A i) (z : ℝ) (j : ℤ)
    {ζ : ℂ} (hζ : ζ ∈ Complex.slitPlane) (hz : limitingEquation r A z j ζ = 0) :
    ∃ δ > 0, ball ζ δ ⊆ Complex.slitPlane ∧ Nonempty (CompactSaddleFamily r A z j ζ δ) := by
  obtain ⟨δ, hδ, hslit, hcompact⟩ := exists_compact_equation_neighborhood hr hA z j hζ
  obtain ⟨_, _, _, C, hC, hzeros⟩ := exists_exact_saddle hr hA z j hζ hz
  have hsmall : ∀ᶠ n : ℕ in atTop, C * smallParameter r n < δ / 4 := by
    have ht : Tendsto (fun n => C * smallParameter r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (smallParameter_tendsto (show 0 < r by omega)).const_mul C
    exact ht.eventually_lt_const (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hzeros.and hsmall)
  obtain ⟨N, hNge, hcont, hhol⟩ := ((eventually_ge_atTop N₀).and hcompact).exists
  have hselect : ∀ b : ℕ, ∃ s ∈ ball ζ (δ / 4),
      exactSaddleEquation r A z j (b + N) s = 0 ∧
      deriv (exactSaddleEquation r A z j (b + N)) s ≠ 0 ∧
      ‖s - ζ‖ ≤ C * smallParameter r (b + N) := by
    intro b
    obtain ⟨hzero, hnear⟩ := hN₀ (b + N) (hNge.trans (Nat.le_add_left N b))
    obtain ⟨s, _, hs, hds, hdist, _⟩ := hzero
    exact ⟨s, by simpa only [mem_ball, dist_eq_norm] using hdist.trans_lt hnear, hs, hds, hdist⟩
  choose σ hmem hzero hsimple herr using hselect
  have hσ : Tendsto σ atTop (𝓝 ζ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun b => norm_nonneg _) herr
      (by simpa only [mul_zero, Function.comp_def] using
        ((smallParameter_tendsto (show 0 < r by omega)).comp (tendsto_add_atTop_nat N)).const_mul C)
  let S : C(OnePoint ℕ, ℂ) := OnePoint.continuousMapMkNat σ ζ hσ
  refine ⟨δ, hδ, hslit, ⟨{
    firstIndex := N
    saddle := S
    errorConstant := C
    errorConstant_nonneg := hC
    saddle_limit := rfl
    saddle_mem := ?_
    equation_zero := ?_
    equation_simple := ?_
    displacement := herr
    continuous_equation := hcont
    holomorphic_equation := hhol }⟩⟩
  · intro q
    cases q with
    | infty => exact mem_ball_self (by positivity)
    | coe b => exact hmem b
  · intro q
    cases q with
    | infty => exact hz
    | coe b => exact hzero b
  · intro q
    cases q with
    | infty =>
      change deriv (limitingEquation r A z j) ζ ≠ 0
      rw [(hasDerivAt_limitingEquation r A z j hζ).deriv]
      exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega : r ≠ 0)) (Complex.slitPlane_ne_zero hζ)
    | coe b => exact hsimple b

namespace CompactSaddleFamily

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}
    (S : CompactSaddleFamily r A z j ζ δ)

include S in
theorem radius_pos : 0 < δ := by
  have h := pos_of_mem_ball (S.saddle_mem ∞)
  linarith

noncomputable def shiftedEquation (t : ℂ) (q : OnePoint ℕ) : ℂ :=
  parameterEquation r A z j S.firstIndex (t + S.saddle q) q

theorem shifted_mem {t : ℂ} (ht : t ∈ ball 0 (δ / 2)) (q : OnePoint ℕ) :
    t + S.saddle q ∈ ball ζ δ := by
  have hσ := S.saddle_mem q
  rw [mem_ball, dist_zero_right] at ht
  rw [mem_ball, dist_eq_norm] at hσ ⊢
  calc
    ‖t + S.saddle q - ζ‖ = ‖t + (S.saddle q - ζ)‖ := by rw [add_sub_assoc]
    _ ≤ ‖t‖ + ‖S.saddle q - ζ‖ := norm_add_le _ _
    _ < δ := by linarith [S.radius_pos]

theorem continuous_shiftedEquation :
    ContinuousOn (Function.uncurry S.shiftedEquation) (ball 0 (δ / 2) ×ˢ univ) := by
  have hshift : Continuous (fun w : ℂ × OnePoint ℕ => (w.1 + S.saddle w.2, w.2)) :=
    (continuous_fst.add (S.saddle.continuous.comp continuous_snd)).prodMk continuous_snd
  exact S.continuous_equation.comp hshift.continuousOn (fun w hw => ⟨S.shifted_mem hw.1 w.2, hw.2⟩)

theorem differentiableOn_shiftedEquation (q : OnePoint ℕ) :
    DifferentiableOn ℂ (fun t => S.shiftedEquation t q) (ball 0 (δ / 2)) :=
  (S.holomorphic_equation q).comp (differentiableOn_id.add_const (S.saddle q))
    (fun _ ht => S.shifted_mem ht q)

@[simp] theorem shiftedEquation_zero (q : OnePoint ℕ) : S.shiftedEquation 0 q = 0 := by
  simpa only [shiftedEquation, zero_add] using S.equation_zero q

theorem shiftedEquation_simple (q : OnePoint ℕ) : deriv (fun t => S.shiftedEquation t q) 0 ≠ 0 := by
  have he := deriv_comp_add_const (fun s => parameterEquation r A z j S.firstIndex s q) (S.saddle q) 0
  exact (by simpa only [shiftedEquation, zero_add] using he) ▸ S.equation_simple q

theorem shiftedEquation_limit (t : ℂ) :
    S.shiftedEquation t ∞ = limitingEquation r A z j (t + ζ) := by
  simp only [shiftedEquation, parameterEquation, Analytic.sequenceFamily_infty, S.saddle_limit]

end CompactSaddleFamily

end ThisWork
