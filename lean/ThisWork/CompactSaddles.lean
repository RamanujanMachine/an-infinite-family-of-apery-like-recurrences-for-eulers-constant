module

public import ThisWork.Argument
public import ThisWork.CompactFamily

/-! A continuous compact family of exact simple saddles and the limiting saddle. -/

@[expose] public section

namespace ThisWork.Analytic


open Set Filter Metric
open scoped Topology OnePoint

noncomputable def parameterEquation [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) (N : ℕ) : ℂ → OnePoint ℕ → ℂ :=
  sequenceFamily (fun m => exactSaddleEquation α₁ α₂ j (m + N))
    (limitingEquation j (saddleScale α₁ α₂))

structure CompactSaddleFamily [PositiveArgument] (α₁ α₂ : ℝ) (j : Branch) where
  firstIndex : ℕ
  saddle : C(OnePoint ℕ, ℂ)
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  saddle_limit : saddle ∞ = (saddleScale α₁ α₂ : ℂ) * rho j
  saddle_mem : ∀ z, saddle z ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 16)
  equation_zero : ∀ z, parameterEquation α₁ α₂ j firstIndex (saddle z) z = 0
  equation_simple : ∀ z, deriv (fun s => parameterEquation α₁ α₂ j firstIndex s z) (saddle z) ≠ 0
  displacement : ∀ m : ℕ,
    ‖saddle m - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ errorConstant * smallParameter (m + firstIndex)
  continuous_equation : ContinuousOn (Function.uncurry (parameterEquation α₁ α₂ j firstIndex))
    (ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8) ×ˢ univ)
  holomorphic_equation : ∀ z, DifferentiableOn ℂ (fun s => parameterEquation α₁ α₂ j firstIndex s z)
    (ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8))

theorem exists_compactSaddleFamily [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (j : Branch) : Nonempty (CompactSaddleFamily α₁ α₂ j) := by
  obtain ⟨r, _, _, C, hC, hzeros⟩ := exists_exact_saddle h₁ h₂ j
  have hsmall : ∀ᶠ n : ℕ in atTop, C * smallParameter n < saddleScale α₁ α₂ / 16 :=
    (show Tendsto (fun n => C * smallParameter n) atTop (𝓝 0) from
      by simpa only [mul_zero] using smallParameter_tendsto.const_mul C).eventually
      (gt_mem_nhds (div_pos (saddleScale_pos h₁ h₂) (by norm_num)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hzeros.and hsmall)
  obtain ⟨N, hNge, hcont, hhol⟩ :=
    ((eventually_ge_atTop N₀).and (eventually_compact_equation_family h₁ h₂ j)).exists
  have hselect : ∀ m : ℕ, ∃ s ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 16),
      exactSaddleEquation α₁ α₂ j (m + N) s = 0 ∧
      deriv (exactSaddleEquation α₁ α₂ j (m + N)) s ≠ 0 ∧
      ‖s - (saddleScale α₁ α₂ : ℂ) * rho j‖ ≤ C * smallParameter (m + N) := by
    intro m
    obtain ⟨hzero, hsmall⟩ := hN₀ (m + N) (hNge.trans (Nat.le_add_left N m))
    obtain ⟨s, _, hz, hd, hdist, _⟩ := hzero
    exact ⟨s, by simpa only [mem_ball, dist_eq_norm] using hdist.trans_lt hsmall, hz, hd, hdist⟩
  choose σ hmem hz hd herr using hselect
  have hσ : Tendsto σ atTop (𝓝 ((saddleScale α₁ α₂ : ℂ) * rho j)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m => norm_nonneg _) herr
      (by simpa only [mul_zero, Function.comp_def] using
        (smallParameter_tendsto.comp (tendsto_add_atTop_nat N)).const_mul C)
  let S : C(OnePoint ℕ, ℂ) := OnePoint.continuousMapMkNat σ ((saddleScale α₁ α₂ : ℂ) * rho j) hσ
  refine ⟨{
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
    holomorphic_equation := hhol }⟩
  · intro z
    cases z with
    | infty => exact mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num))
    | coe m => exact hmem m
  · intro z
    cases z with
    | infty => exact limitingEquation_saddle j (saddleScale_pos h₁ h₂)
    | coe m => exact hz m
  · intro z
    cases z with
    | infty => exact limitingEquation_saddle_simple j (saddleScale_pos h₁ h₂)
    | coe m => exact hd m

namespace CompactSaddleFamily

theorem saddle_mem_disk [PositiveArgument] {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) : S.saddle z ∈ saddleDisk (saddleScale α₁ α₂) j :=
  ball_subset_closedBall (ball_subset_ball
    (by linarith [saddleScale_pos h₁ h₂] : saddleScale α₁ α₂ / 16 ≤ saddleScale α₁ α₂ / 4) (S.saddle_mem z))

noncomputable def shiftedEquation [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} (S : CompactSaddleFamily α₁ α₂ j)
    (t : ℂ) (z : OnePoint ℕ) : ℂ :=
  parameterEquation α₁ α₂ j S.firstIndex (t + S.saddle z) z

theorem shifted_mem [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} (S : CompactSaddleFamily α₁ α₂ j)
    {t : ℂ} (ht : t ∈ ball 0 (saddleScale α₁ α₂ / 16)) (z : OnePoint ℕ) :
    t + S.saddle z ∈ ball ((saddleScale α₁ α₂ : ℂ) * rho j) (saddleScale α₁ α₂ / 8) := by
  have hσ := S.saddle_mem z
  rw [mem_ball, dist_zero_right] at ht
  rw [mem_ball, dist_eq_norm] at hσ ⊢
  calc
    ‖t + S.saddle z - (saddleScale α₁ α₂ : ℂ) * rho j‖ =
        ‖t + (S.saddle z - (saddleScale α₁ α₂ : ℂ) * rho j)‖ := by rw [add_sub_assoc]
    _ ≤ ‖t‖ + ‖S.saddle z - (saddleScale α₁ α₂ : ℂ) * rho j‖ := norm_add_le _ _
    _ < saddleScale α₁ α₂ / 8 := by linarith

theorem continuous_shiftedEquation [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) :
    ContinuousOn (Function.uncurry S.shiftedEquation) (ball 0 (saddleScale α₁ α₂ / 16) ×ˢ univ) := by
  have hshift : Continuous (fun w : ℂ × OnePoint ℕ => (w.1 + S.saddle w.2, w.2)) :=
    (continuous_fst.add (S.saddle.continuous.comp continuous_snd)).prodMk continuous_snd
  exact S.continuous_equation.comp hshift.continuousOn (fun w hw => ⟨S.shifted_mem hw.1 w.2, hw.2⟩)

theorem differentiableOn_shiftedEquation [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    DifferentiableOn ℂ (fun t => S.shiftedEquation t z) (ball 0 (saddleScale α₁ α₂ / 16)) :=
  (S.holomorphic_equation z).comp (differentiableOn_id.add_const (S.saddle z))
    (fun _ ht => S.shifted_mem ht z)

@[simp] theorem shiftedEquation_zero [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) : S.shiftedEquation 0 z = 0 := by
  simpa only [shiftedEquation, zero_add] using S.equation_zero z

theorem shiftedEquation_simple [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (z : OnePoint ℕ) :
    deriv (fun t => S.shiftedEquation t z) 0 ≠ 0 := by
  have he := deriv_comp_add_const (fun s => parameterEquation α₁ α₂ j S.firstIndex s z) (S.saddle z) 0
  exact (by simpa only [shiftedEquation, zero_add] using he) ▸ S.equation_simple z

theorem shiftedEquation_limit [PositiveArgument] {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (t : ℂ) :
    S.shiftedEquation t ∞ = limitingEquation j (saddleScale α₁ α₂)
      (t + (saddleScale α₁ α₂ : ℂ) * rho j) := by
  simp only [shiftedEquation, parameterEquation, sequenceFamily_infty, S.saddle_limit]

end CompactSaddleFamily

end ThisWork.Analytic
