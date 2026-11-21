module
public import ThisWork.QuadraticSaddleFamily
public import ThisWork.NormalizedLocalMoments
/-! Uniform local Gaussian moment estimates for an arbitrary compact saddle family. -/
@[expose] public section
namespace ThisWork.Analytic
open Set Filter Metric
open scoped Topology OnePoint
namespace QuadraticSaddleFamily

structure LocalSaddleData  (S : QuadraticSaddleFamily) where
  shift : ℕ
  speed : ℝ
  speed_pos : 0 < speed
  positive : Neuschel.LocalContourModel 2 0 ((speed : ℂ) * S.tangent)
    (fun z => S.phaseCoefficients 0 (parameterShift shift z))
    (fun t z => S.phase t (parameterShift shift z)) (ball 0 (S.radius))
    (fun u : ℝ => (u : ℂ) * ((speed : ℂ) * S.tangent))
  negative : Neuschel.LocalContourModel 2 0 (-((speed : ℂ) * S.tangent))
    (fun z => S.phaseCoefficients 0 (parameterShift shift z))
    (fun t z => S.phase t (parameterShift shift z)) (ball 0 (S.radius))
    (fun u : ℝ => (u : ℂ) * (-((speed : ℂ) * S.tangent)))

theorem exists_localSaddleData 
    (S : QuadraticSaddleFamily) : Nonempty S.LocalSaddleData := by
  obtain ⟨N, d, hd, hM⟩ := S.exists_local_saddle_contour_models
  have hp := hM 1 (Or.inl rfl)
  have hm := hM (-1) (Or.inr rfl)
  simp only [one_mul] at hp
  simp only [Complex.ofReal_neg, neg_mul, one_mul] at hm
  exact ⟨⟨N, d, hd, hp.some, hm.some⟩⟩

noncomputable def momentAmplitude 
    (S : QuadraticSaddleFamily) (N k : ℕ) (t : ℂ) (z : OnePoint ℕ) : ℂ :=
  (t + S.saddle (parameterShift N z)) ^ k

theorem continuous_momentAmplitude 
    (S : QuadraticSaddleFamily) (N k : ℕ) :
    Continuous (Function.uncurry (S.momentAmplitude N k)) := by
  change Continuous (fun w : ℂ × OnePoint ℕ => (w.1 + S.saddle (parameterShift N w.2)) ^ k)
  exact (continuous_fst.add (S.saddle.continuous.comp
    ((parameterShift N).continuous.comp continuous_snd))).pow k

theorem differentiableOn_momentAmplitude 
    (S : QuadraticSaddleFamily) (N k : ℕ) (z : OnePoint ℕ) (G : Set ℂ) :
    DifferentiableOn ℂ (fun t => S.momentAmplitude N k t z) G :=
  (differentiableOn_id.add_const (S.saddle (parameterShift N z))).pow k

namespace LocalSaddleData

noncomputable def velocity  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) : ℂ := (D.speed : ℂ) * S.tangent

theorem velocity_ne_zero  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) : D.velocity ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr D.speed_pos.ne') (S.tangent_ne_zero)

noncomputable def leftWidth  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) : ℝ := D.speed * D.negative.cutoff

noncomputable def rightWidth  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) : ℝ := D.speed * D.positive.cutoff

theorem widths_pos  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) : 0 < D.leftWidth ∧ 0 < D.rightWidth :=
  ⟨mul_pos D.speed_pos D.negative.cutoff_mem.1, mul_pos D.speed_pos D.positive.cutoff_mem.1⟩

theorem widths_lt  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) : D.leftWidth < S.radius ∧
      D.rightWidth < S.radius := by
  have hp := D.positive.inverseFamily.source_subset
    (D.positive.contour_in_source D.positive.cutoff
      (right_mem_Icc.mpr D.positive.cutoff_mem.1.le) ∞).1
  have hm := D.negative.inverseFamily.source_subset
    (D.negative.contour_in_source D.negative.cutoff
      (right_mem_Icc.mpr D.negative.cutoff_mem.1.le) ∞).1
  simp only [mem_ball, dist_zero_right, norm_mul, S.norm_tangent, mul_one,
    Complex.norm_of_nonneg D.speed_pos.le,
    Complex.norm_of_nonneg D.positive.cutoff_mem.1.le] at hp
  simp only [mem_ball, dist_zero_right, norm_mul, norm_neg, S.norm_tangent, mul_one,
    Complex.norm_of_nonneg D.speed_pos.le,
    Complex.norm_of_nonneg D.negative.cutoff_mem.1.le] at hm
  exact ⟨by simpa only [leftWidth, mul_comm] using hm,
    by simpa only [rightWidth, mul_comm] using hp⟩

noncomputable def localMoment  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) (R : ℝ) (k : ℕ) (z : OnePoint ℕ) : ℂ :=
  (∫ u in 0..D.positive.cutoff, D.velocity *
    (Complex.exp (-(R : ℂ) * S.phase ((u : ℂ) * D.velocity) (parameterShift D.shift z)) *
      S.momentAmplitude D.shift k ((u : ℂ) * D.velocity) z)) -
  (∫ u in 0..D.negative.cutoff, (-D.velocity) *
    (Complex.exp (-(R : ℂ) * S.phase ((u : ℂ) * (-D.velocity)) (parameterShift D.shift z)) *
      S.momentAmplitude D.shift k ((u : ℂ) * (-D.velocity)) z))

theorem local_moment_leading_estimate 
    {S : QuadraticSaddleFamily} (D : S.LocalSaddleData) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ z,
      ‖D.localMoment R k z - S.saddle (parameterShift D.shift z) ^ k *
        (Neuschel.leadingRoot 2 D.velocity (S.phaseCoefficients 0 (parameterShift D.shift z)))⁻¹ *
          ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ C * R ^ (-1 : ℝ) := by
  have hb := D.positive.two_sided_quadratic_leading_estimate D.negative isOpen_ball
    (mem_ball_self S.radius_pos) D.velocity_ne_zero
    (fun z => S.differentiableOn_phase (parameterShift D.shift z))
    (S.continuous_momentAmplitude D.shift k).continuousOn
    (fun z => S.differentiableOn_momentAmplitude D.shift k z _)
  simpa only [localMoment, velocity, S.phase_zero, sub_zero, momentAmplitude, zero_add] using hb

end LocalSaddleData

end QuadraticSaddleFamily

end ThisWork.Analytic

namespace ThisWork.Analytic.QuadraticSaddleFamily.LocalSaddleData



open Set Filter Metric
open scoped Topology OnePoint

noncomputable def quadraticRoot  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) (z : OnePoint ℕ) : ℂ :=
  Neuschel.leadingRoot 2 D.velocity (S.phaseCoefficients 0 (parameterShift D.shift z))

noncomputable def normalizedLocalMoment  {S : QuadraticSaddleFamily}
    (D : S.LocalSaddleData) (R : ℝ) (k : ℕ) (z : OnePoint ℕ) : ℂ :=
  D.quadraticRoot z * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) * D.localMoment R k z

theorem uniform_quadraticRoot_bounds 
    {S : QuadraticSaddleFamily} (D : S.LocalSaddleData) :
    ∃ B ≥ 1, ∀ z, ‖D.quadraticRoot z‖ ≤ B ∧ ‖(D.quadraticRoot z)⁻¹‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := Neuschel.exists_uniform_quadratic_root_bounds
    (S.continuous_phaseCoefficients 0) (S.phaseCoefficients_zero_ne) D.velocity_ne_zero
  exact ⟨B, hB, fun z => hb (parameterShift D.shift z)⟩

theorem normalized_local_moment_error 
    {S : QuadraticSaddleFamily} (D : S.LocalSaddleData) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ z,
      ‖D.normalizedLocalMoment R k z - S.saddle (parameterShift D.shift z) ^ k‖ ≤
        C * R ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := D.uniform_quadraticRoot_bounds
  obtain ⟨C, hC, hc⟩ := D.local_moment_leading_estimate k
  have hG : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨B * C / Real.Gamma (1 / 2 : ℝ), by positivity, ?_⟩
  filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with R hR hR0 z
  have hroot : D.quadraticRoot z ≠ 0 := Neuschel.leadingRoot_ne_zero 2 D.velocity_ne_zero _
  have hp : 0 < R ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hR0 _
  have hcancel : D.quadraticRoot z * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) *
      (S.saddle (parameterShift D.shift z) ^ k * (D.quadraticRoot z)⁻¹ *
        ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      S.saddle (parameterShift D.shift z) ^ k := by
    push_cast
    field_simp [hroot, Complex.ofReal_ne_zero.mpr hG.ne', Complex.ofReal_ne_zero.mpr hp.ne']
    exact mul_div_cancel_left₀ _
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne') (Complex.ofReal_ne_zero.mpr hG.ne'))
  have he : D.normalizedLocalMoment R k z - S.saddle (parameterShift D.shift z) ^ k =
      (D.quadraticRoot z * ((R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ)) *
      (D.localMoment R k z - S.saddle (parameterShift D.shift z) ^ k * (D.quadraticRoot z)⁻¹ *
        ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
    rw [mul_sub, hcancel]
    rfl
  rw [he, norm_mul, norm_mul, Complex.norm_of_nonneg (div_pos hp hG).le]
  calc
    _ ≤ (B * (R ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2 : ℝ))) * (C * R ^ (-1 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hb z).1 (div_pos hp hG).le)
        (hR z) (norm_nonneg _) (by positivity)
    _ = (B * C / Real.Gamma (1 / 2 : ℝ)) * (R ^ (1 / 2 : ℝ) * R ^ (-1 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hR0]; norm_num


end ThisWork.Analytic.QuadraticSaddleFamily.LocalSaddleData
