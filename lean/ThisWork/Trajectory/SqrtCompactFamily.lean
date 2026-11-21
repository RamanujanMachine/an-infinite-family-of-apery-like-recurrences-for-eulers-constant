module
public import ThisWork.Trajectory.SqrtLocalPhase
public import ThisWork.QuadraticSaddleMoments
/-! The square-root saddle equations as a compact family. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology OnePoint
/-- The exact saddle equations and their limit form a jointly continuous,
holomorphic family on a common disk with compact parameter space. -/
theorem eventually_compact_sqrt_equation_family {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) :
    ∀ᶠ N : ℕ in atTop,
      ContinuousOn (Function.uncurry (sequenceFamily
        (fun m => exactSqrtEquation d A₁ A₂ z .three (m + N))
        (sqrtEquation (doubleSaddleScale d A₁ A₂ z))))
        (ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8) ×ˢ univ) ∧
      ∀ w : OnePoint ℕ, DifferentiableOn ℂ
        (fun s => sequenceFamily (fun m => exactSqrtEquation d A₁ A₂ z .three (m + N))
          (sqrtEquation (doubleSaddleScale d A₁ A₂ z)) s w)
        (ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_differentiableOn_exactSqrtEquation h₁ h₂ hz (doubleSaddleScale_pos hd h₁ h₂ hz) d .three)
  filter_upwards [eventually_ge_atTop N₀] with N hNge
  have hN := fun n (hn : N ≤ n) => hN₀ n (hNge.trans hn)
  have hc := doubleSaddleScale_pos hd h₁ h₂ hz
  have hsub : closedBall (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8) ⊆
      ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 4) :=
    closedBall_subset_ball (by linarith)
  have hlim : TendstoUniformlyOn (fun m => exactSqrtEquation d A₁ A₂ z .three (m + N))
      (sqrtEquation (doubleSaddleScale d A₁ A₂ z)) atTop
      (closedBall (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8)) :=
    ((exactSqrtEquation_tendsto_uniform_disk hd h₁ h₂ hz).mono
      (fun s hs => by
        simpa only [Analytic.saddleDisk, rho_three, mul_one] using ball_subset_closedBall (hsub hs))).seq_tendstoUniformlyOn
        (fun m => m + N) (tendsto_add_atTop_nat N)
  have hcont := continuousOn_sequenceFamily (isCompact_closedBall _ _)
    (fun m => ((hN (m + N) (Nat.le_add_left N m)).mono hsub).continuousOn)
    (((differentiableOn_sqrtEquation_disk hc).mono hsub).continuousOn) hlim
  refine ⟨hcont.mono (Set.prod_mono ball_subset_closedBall Subset.rfl), ?_⟩
  intro w
  cases w with
  | infty =>
    exact (differentiableOn_sqrtEquation_disk hc).mono
      (fun s hs => hsub (ball_subset_closedBall hs))
  | coe m =>
    exact (hN (m + N) (Nat.le_add_left N m)).mono
      (fun s hs => hsub (ball_subset_closedBall hs))

noncomputable def sqrtParameterEquation  (d : ℕ) (A₁ A₂ z : ℝ) (N : ℕ) : ℂ → OnePoint ℕ → ℂ :=
  sequenceFamily (fun m => exactSqrtEquation d A₁ A₂ z .three (m + N))
    (sqrtEquation (doubleSaddleScale d A₁ A₂ z))

structure SqrtSaddleFamily  (d : ℕ) (A₁ A₂ z : ℝ) where
  firstIndex : ℕ
  saddle : C(OnePoint ℕ, ℂ)
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  saddle_limit : saddle ∞ = (doubleSaddleScale d A₁ A₂ z : ℂ)
  saddle_mem : ∀ w, saddle w ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 16)
  equation_zero : ∀ w, sqrtParameterEquation d A₁ A₂ z firstIndex (saddle w) w = 0
  equation_simple : ∀ w, deriv (fun s => sqrtParameterEquation d A₁ A₂ z firstIndex s w) (saddle w) ≠ 0
  displacement : ∀ m : ℕ,
    ‖saddle m - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ errorConstant / sqrtScale (m + firstIndex)
  continuous_equation : ContinuousOn (Function.uncurry (sqrtParameterEquation d A₁ A₂ z firstIndex))
    (ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8) ×ˢ univ)
  holomorphic_equation : ∀ w, DifferentiableOn ℂ (fun s => sqrtParameterEquation d A₁ A₂ z firstIndex s w)
    (ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8))

theorem exists_compactSaddleFamily  {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) : Nonempty (SqrtSaddleFamily d A₁ A₂ z) := by
  obtain ⟨r, _, _, C, hC, hzeros⟩ := exists_exact_sqrt_saddle hd h₁ h₂ hz
  have hsmall : ∀ᶠ n : ℕ in atTop, C / sqrtScale n < doubleSaddleScale d A₁ A₂ z / 16 :=
    (show Tendsto (fun n => C / sqrtScale n) atTop (𝓝 0) from
      by simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using (tendsto_inv_atTop_zero.comp sqrtScale_tendsto).const_mul C).eventually
      (gt_mem_nhds (div_pos (doubleSaddleScale_pos hd h₁ h₂ hz) (by norm_num)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hzeros.and hsmall)
  obtain ⟨N, hNge, hcont, hhol⟩ :=
    ((eventually_ge_atTop N₀).and (eventually_compact_sqrt_equation_family hd h₁ h₂ hz)).exists
  have hselect : ∀ m : ℕ, ∃ s ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 16),
      exactSqrtEquation d A₁ A₂ z .three (m + N) s = 0 ∧
      deriv (exactSqrtEquation d A₁ A₂ z .three (m + N)) s ≠ 0 ∧
      ‖s - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ ≤ C / sqrtScale (m + N) := by
    intro m
    obtain ⟨hzero, hsmall⟩ := hN₀ (m + N) (hNge.trans (Nat.le_add_left N m))
    obtain ⟨s, _, hz, hd, hdist, _⟩ := hzero
    exact ⟨s, by simpa only [mem_ball, dist_eq_norm] using hdist.trans_lt hsmall, hz, hd, hdist⟩
  choose σ hmem hzero hder herr using hselect
  have hσ : Tendsto σ atTop (𝓝 (doubleSaddleScale d A₁ A₂ z : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m => norm_nonneg _) herr
      (by simpa only [mul_zero, Function.comp_def, div_eq_mul_inv] using
        ((tendsto_inv_atTop_zero.comp sqrtScale_tendsto).comp (tendsto_add_atTop_nat N)).const_mul C)
  let S : C(OnePoint ℕ, ℂ) := OnePoint.continuousMapMkNat σ (doubleSaddleScale d A₁ A₂ z : ℂ) hσ
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
  · intro w
    cases w with
    | infty => exact mem_ball_self (div_pos (doubleSaddleScale_pos hd h₁ h₂ hz) (by norm_num))
    | coe m => exact hmem m
  · intro w
    cases w with
    | infty => exact sqrtEquation_saddle (doubleSaddleScale_pos hd h₁ h₂ hz)
    | coe m => exact hzero m
  · intro w
    cases w with
    | infty => exact sqrtEquation_saddle_simple (doubleSaddleScale_pos hd h₁ h₂ hz)
    | coe m => exact hder m

namespace SqrtSaddleFamily

theorem saddle_mem_disk  {d : ℕ} {A₁ A₂ z : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (S : SqrtSaddleFamily d A₁ A₂ z) (w : OnePoint ℕ) : S.saddle w ∈ saddleDisk (doubleSaddleScale d A₁ A₂ z) .three :=
  by
  simpa only [saddleDisk, rho_three, mul_one] using ball_subset_closedBall (ball_subset_ball
    (by linarith [doubleSaddleScale_pos hd h₁ h₂ hz] : doubleSaddleScale d A₁ A₂ z / 16 ≤ doubleSaddleScale d A₁ A₂ z / 4) (S.saddle_mem w))

noncomputable def shiftedEquation  {d : ℕ} {A₁ A₂ z : ℝ} (S : SqrtSaddleFamily d A₁ A₂ z)
    (t : ℂ) (w : OnePoint ℕ) : ℂ :=
  sqrtParameterEquation d A₁ A₂ z S.firstIndex (t + S.saddle w) w

theorem shifted_mem  {d : ℕ} {A₁ A₂ z : ℝ} (S : SqrtSaddleFamily d A₁ A₂ z)
    {t : ℂ} (ht : t ∈ ball 0 (doubleSaddleScale d A₁ A₂ z / 16)) (w : OnePoint ℕ) :
    t + S.saddle w ∈ ball (doubleSaddleScale d A₁ A₂ z : ℂ) (doubleSaddleScale d A₁ A₂ z / 8) := by
  have hσ := S.saddle_mem w
  rw [mem_ball, dist_zero_right] at ht
  rw [mem_ball, dist_eq_norm] at hσ ⊢
  calc
    ‖t + S.saddle w - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ =
        ‖t + (S.saddle w - (doubleSaddleScale d A₁ A₂ z : ℂ))‖ := by rw [add_sub_assoc]
    _ ≤ ‖t‖ + ‖S.saddle w - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ := norm_add_le _ _
    _ < doubleSaddleScale d A₁ A₂ z / 8 := by linarith

theorem continuous_shiftedEquation  {d : ℕ} {A₁ A₂ z : ℝ} (S : SqrtSaddleFamily d A₁ A₂ z) :
    ContinuousOn (Function.uncurry S.shiftedEquation) (ball 0 (doubleSaddleScale d A₁ A₂ z / 16) ×ˢ univ) := by
  have hshift : Continuous (fun w : ℂ × OnePoint ℕ => (w.1 + S.saddle w.2, w.2)) :=
    (continuous_fst.add (S.saddle.continuous.comp continuous_snd)).prodMk continuous_snd
  exact S.continuous_equation.comp hshift.continuousOn (fun w hw => ⟨S.shifted_mem hw.1 w.2, hw.2⟩)

theorem differentiableOn_shiftedEquation  {d : ℕ} {A₁ A₂ z : ℝ}
    (S : SqrtSaddleFamily d A₁ A₂ z) (w : OnePoint ℕ) :
    DifferentiableOn ℂ (fun t => S.shiftedEquation t w) (ball 0 (doubleSaddleScale d A₁ A₂ z / 16)) :=
  (S.holomorphic_equation w).comp (differentiableOn_id.add_const (S.saddle w))
    (fun _ ht => S.shifted_mem ht w)

@[simp] theorem shiftedEquation_zero  {d : ℕ} {A₁ A₂ z : ℝ}
    (S : SqrtSaddleFamily d A₁ A₂ z) (w : OnePoint ℕ) : S.shiftedEquation 0 w = 0 := by
  simpa only [shiftedEquation, zero_add] using S.equation_zero w

theorem shiftedEquation_simple  {d : ℕ} {A₁ A₂ z : ℝ}
    (S : SqrtSaddleFamily d A₁ A₂ z) (w : OnePoint ℕ) :
    deriv (fun t => S.shiftedEquation t w) 0 ≠ 0 := by
  have he := deriv_comp_add_const (fun s => sqrtParameterEquation d A₁ A₂ z S.firstIndex s w) (S.saddle w) 0
  exact (by simpa only [shiftedEquation, zero_add] using he) ▸ S.equation_simple w

theorem shiftedEquation_limit  {d : ℕ} {A₁ A₂ z : ℝ}
    (S : SqrtSaddleFamily d A₁ A₂ z) (t : ℂ) :
    S.shiftedEquation t ∞ = sqrtEquation (doubleSaddleScale d A₁ A₂ z)
      (t + (doubleSaddleScale d A₁ A₂ z : ℂ)) := by
  simp only [shiftedEquation, sqrtParameterEquation, sequenceFamily_infty, S.saddle_limit]

end SqrtSaddleFamily

end ThisWork.Trajectory
