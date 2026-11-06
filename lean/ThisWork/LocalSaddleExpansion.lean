module

public import ThisWork.LocalSaddleContours
public import Neuschel.QuadraticExpansion

/-! Two-sided local expansions with the actual moving saddle moment amplitudes. -/

@[expose] public section

namespace ThisWork

open Set Filter Metric
open scoped Topology OnePoint

namespace CompactSaddleFamily

structure LocalSaddleData {α₁ α₂ : ℝ} {j : Branch} (S : CompactSaddleFamily α₁ α₂ j) where
  shift : ℕ
  speed : ℝ
  speed_pos : 0 < speed
  positive : Neuschel.LocalContourModel 2 0 ((speed : ℂ) * saddleTangent j)
    (fun z => S.phaseCoefficients 0 (parameterShift shift z))
    (fun t z => S.phase t (parameterShift shift z)) (ball 0 (saddleScale α₁ α₂ / 16))
    (fun u : ℝ => (u : ℂ) * ((speed : ℂ) * saddleTangent j))
  negative : Neuschel.LocalContourModel 2 0 (-((speed : ℂ) * saddleTangent j))
    (fun z => S.phaseCoefficients 0 (parameterShift shift z))
    (fun t z => S.phase t (parameterShift shift z)) (ball 0 (saddleScale α₁ α₂ / 16))
    (fun u : ℝ => (u : ℂ) * (-((speed : ℂ) * saddleTangent j)))

theorem exists_localSaddleData {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) : Nonempty S.LocalSaddleData := by
  obtain ⟨N, d, hd, hM⟩ := S.exists_local_saddle_contour_models h₁ h₂
  have hp := hM 1 (Or.inl rfl)
  have hm := hM (-1) (Or.inr rfl)
  simp only [one_mul] at hp
  simp only [Complex.ofReal_neg, neg_mul, one_mul] at hm
  exact ⟨⟨N, d, hd, hp.some, hm.some⟩⟩

noncomputable def momentAmplitude {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (N k : ℕ) (t : ℂ) (z : OnePoint ℕ) : ℂ :=
  (t + S.saddle (parameterShift N z)) ^ k

theorem continuous_momentAmplitude {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (N k : ℕ) :
    Continuous (Function.uncurry (S.momentAmplitude N k)) := by
  change Continuous (fun w : ℂ × OnePoint ℕ => (w.1 + S.saddle (parameterShift N w.2)) ^ k)
  exact (continuous_fst.add (S.saddle.continuous.comp
    ((parameterShift N).continuous.comp continuous_snd))).pow k

theorem differentiableOn_momentAmplitude {α₁ α₂ : ℝ} {j : Branch}
    (S : CompactSaddleFamily α₁ α₂ j) (N k : ℕ) (z : OnePoint ℕ) (G : Set ℂ) :
    DifferentiableOn ℂ (fun t => S.momentAmplitude N k t z) G :=
  (differentiableOn_id.add_const (S.saddle (parameterShift N z))).pow k

namespace LocalSaddleData

noncomputable def velocity {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : ℂ := (D.speed : ℂ) * saddleTangent j

theorem velocity_ne_zero {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : D.velocity ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr D.speed_pos.ne') (saddleTangent_ne_zero j)

noncomputable def leftWidth {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : ℝ := D.speed * D.negative.cutoff

noncomputable def rightWidth {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : ℝ := D.speed * D.positive.cutoff

theorem widths_pos {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : 0 < D.leftWidth ∧ 0 < D.rightWidth :=
  ⟨mul_pos D.speed_pos D.negative.cutoff_mem.1, mul_pos D.speed_pos D.positive.cutoff_mem.1⟩

theorem widths_lt {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) : D.leftWidth < saddleScale α₁ α₂ / 16 ∧
      D.rightWidth < saddleScale α₁ α₂ / 16 := by
  have hp := D.positive.inverseFamily.source_subset
    (D.positive.contour_in_source D.positive.cutoff
      (right_mem_Icc.mpr D.positive.cutoff_mem.1.le) ∞).1
  have hm := D.negative.inverseFamily.source_subset
    (D.negative.contour_in_source D.negative.cutoff
      (right_mem_Icc.mpr D.negative.cutoff_mem.1.le) ∞).1
  simp only [mem_ball, dist_zero_right, norm_mul, norm_saddleTangent, mul_one,
    Complex.norm_of_nonneg D.speed_pos.le,
    Complex.norm_of_nonneg D.positive.cutoff_mem.1.le] at hp
  simp only [mem_ball, dist_zero_right, norm_mul, norm_neg, norm_saddleTangent, mul_one,
    Complex.norm_of_nonneg D.speed_pos.le,
    Complex.norm_of_nonneg D.negative.cutoff_mem.1.le] at hm
  exact ⟨by simpa only [leftWidth, mul_comm] using hm,
    by simpa only [rightWidth, mul_comm] using hp⟩

noncomputable def localMoment {α₁ α₂ : ℝ} {j : Branch} {S : CompactSaddleFamily α₁ α₂ j}
    (D : S.LocalSaddleData) (R : ℝ) (k : ℕ) (z : OnePoint ℕ) : ℂ :=
  (∫ u in 0..D.positive.cutoff, D.velocity *
    (Complex.exp (-(R : ℂ) * S.phase ((u : ℂ) * D.velocity) (parameterShift D.shift z)) *
      S.momentAmplitude D.shift k ((u : ℂ) * D.velocity) z)) -
  (∫ u in 0..D.negative.cutoff, (-D.velocity) *
    (Complex.exp (-(R : ℂ) * S.phase ((u : ℂ) * (-D.velocity)) (parameterShift D.shift z)) *
      S.momentAmplitude D.shift k ((u : ℂ) * (-D.velocity)) z))

theorem local_moment_leading_estimate {α₁ α₂ : ℝ} (h₁ : 0 < α₁) (h₂ : 0 < α₂) {j : Branch}
    {S : CompactSaddleFamily α₁ α₂ j} (D : S.LocalSaddleData) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ z,
      ‖D.localMoment R k z - S.saddle (parameterShift D.shift z) ^ k *
        (Neuschel.leadingRoot 2 D.velocity (S.phaseCoefficients 0 (parameterShift D.shift z)))⁻¹ *
          ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ C * R ^ (-1 : ℝ) := by
  have hb := D.positive.two_sided_quadratic_leading_estimate D.negative isOpen_ball
    (mem_ball_self (div_pos (saddleScale_pos h₁ h₂) (by norm_num))) D.velocity_ne_zero
    (fun z => S.differentiableOn_phase h₁ h₂ (parameterShift D.shift z))
    (S.continuous_momentAmplitude D.shift k).continuousOn
    (fun z => S.differentiableOn_momentAmplitude D.shift k z _)
  simpa only [localMoment, velocity, S.phase_zero, sub_zero, momentAmplitude, zero_add] using hb

end LocalSaddleData

end CompactSaddleFamily

end ThisWork
