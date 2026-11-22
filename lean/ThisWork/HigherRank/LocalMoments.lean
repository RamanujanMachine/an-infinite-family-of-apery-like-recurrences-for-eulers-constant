module

public import ThisWork.HigherRank.ParabolicLocalContours

/-! Two-sided local moment asymptotics on actual parabolic saddle windows. -/

@[expose] public section
namespace ThisWork.HigherRank.CompactSaddleFamily

open Set Filter Metric
open scoped Topology OnePoint

variable {r : ℕ} {A : Fin (r - 1) → ℝ} {z : ℝ} {j : ℤ} {ζ : ℂ} {δ : ℝ}

structure LocalParabolicData (S : CompactSaddleFamily r A z j ζ δ) (v : ℂ) where
  shift : ℕ
  speed : ℝ
  speed_pos : 0 < speed
  positive : Neuschel.LocalContourModel 2 0 ((speed : ℂ) * v)
    (fun q => S.phaseCoefficients 0 (Analytic.parameterShift shift q))
    (fun t q => S.phase t (Analytic.parameterShift shift q)) (ball 0 (δ / 2))
    (fun u : ℝ => quadraticArc v ((u : ℂ) * (speed : ℂ)))
  negative : Neuschel.LocalContourModel 2 0 (-((speed : ℂ) * v))
    (fun q => S.phaseCoefficients 0 (Analytic.parameterShift shift q))
    (fun t q => S.phase t (Analytic.parameterShift shift q)) (ball 0 (δ / 2))
    (fun u : ℝ => quadraticArc v ((u : ℂ) * (-speed : ℂ)))

theorem exists_localParabolicData (S : CompactSaddleFamily r A z j ζ δ) {v : ℂ}
    (hpos : 0 < (S.phaseCoefficients 0 ∞ * v ^ 2).re) : Nonempty (S.LocalParabolicData v) := by
  obtain ⟨N, d, hd, hmodels⟩ := S.exists_local_parabolic_models hpos
  have hp := hmodels 1 (Or.inl rfl)
  have hm := hmodels (-1) (Or.inr rfl)
  simp only [one_mul] at hp
  simp only [Complex.ofReal_neg, neg_mul, one_mul] at hm
  exact ⟨⟨N, d, hd, hp.some, hm.some⟩⟩

noncomputable def momentAmplitude (S : CompactSaddleFamily r A z j ζ δ)
    (N k : ℕ) (t : ℂ) (q : OnePoint ℕ) : ℂ :=
  (t + S.saddle (Analytic.parameterShift N q)) ^ k

theorem continuous_momentAmplitude (S : CompactSaddleFamily r A z j ζ δ) (N k : ℕ) :
    Continuous (Function.uncurry (S.momentAmplitude N k)) := by
  change Continuous (fun w : ℂ × OnePoint ℕ => (w.1 + S.saddle (Analytic.parameterShift N w.2)) ^ k)
  exact (continuous_fst.add (S.saddle.continuous.comp
    ((Analytic.parameterShift N).continuous.comp continuous_snd))).pow k

theorem differentiableOn_momentAmplitude (S : CompactSaddleFamily r A z j ζ δ)
    (N k : ℕ) (q : OnePoint ℕ) (G : Set ℂ) :
    DifferentiableOn ℂ (fun t => S.momentAmplitude N k t q) G :=
  (differentiableOn_id.add_const (S.saddle (Analytic.parameterShift N q))).pow k

namespace LocalParabolicData

variable {S : CompactSaddleFamily r A z j ζ δ} {v : ℂ} (D : S.LocalParabolicData v)

noncomputable def halfMoment (R : ℝ) (k : ℕ) (q : OnePoint ℕ) (d cutoff : ℝ) : ℂ :=
  ∫ u in 0..cutoff, ((d : ℂ) * (v - 2 * ((u : ℂ) * (d : ℂ)))) *
    (Complex.exp (-(R : ℂ) * S.phase (quadraticArc v ((u : ℂ) * (d : ℂ)))
      (Analytic.parameterShift D.shift q)) *
      S.momentAmplitude D.shift k (quadraticArc v ((u : ℂ) * (d : ℂ))) q)

noncomputable def localMoment (R : ℝ) (k : ℕ) (q : OnePoint ℕ) : ℂ :=
  D.halfMoment R k q D.speed D.positive.cutoff -
    D.halfMoment R k q (-D.speed) D.negative.cutoff

theorem local_moment_leading_estimate (hv : v ≠ 0) (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ R : ℝ in atTop, ∀ q : OnePoint ℕ,
      ‖D.localMoment R k q - S.saddle (Analytic.parameterShift D.shift q) ^ k *
        (Neuschel.leadingRoot 2 ((D.speed : ℂ) * v)
          (S.phaseCoefficients 0 (Analytic.parameterShift D.shift q)))⁻¹ *
          ((Real.Gamma (1 / 2 : ℝ) / R ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ C * R ^ (-1 : ℝ) := by
  have hvel : (D.speed : ℂ) * v ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr D.speed_pos.ne') hv
  obtain ⟨Cp, hCp, hp⟩ := D.positive.quadratic_curve_leading_estimate
    (velocity := fun u => (D.speed : ℂ) * (v - 2 * ((u : ℂ) * (D.speed : ℂ)))) isOpen_ball
    (mem_ball_self (half_pos S.radius_pos)) hvel
    (fun q => S.differentiableOn_phase (Analytic.parameterShift D.shift q))
    (S.continuous_momentAmplitude D.shift k).continuousOn
    (fun q => S.differentiableOn_momentAmplitude D.shift k q _)
    (by simp) (by unfold quadraticArc; fun_prop) (by fun_prop)
    (fun u _ => hasDerivAt_scaled_quadraticArc v D.speed u)
  obtain ⟨Cm, hCm, hm⟩ := D.negative.quadratic_curve_leading_estimate
    (velocity := fun u => (-D.speed : ℂ) * (v - 2 * ((u : ℂ) * (-D.speed : ℂ)))) isOpen_ball
    (mem_ball_self (half_pos S.radius_pos)) (neg_ne_zero.mpr hvel)
    (fun q => S.differentiableOn_phase (Analytic.parameterShift D.shift q))
    (S.continuous_momentAmplitude D.shift k).continuousOn
    (fun q => S.differentiableOn_momentAmplitude D.shift k q _)
    (by simp) (by unfold quadraticArc; fun_prop) (by fun_prop)
    (fun u _ => by simpa only [Complex.ofReal_neg] using hasDerivAt_scaled_quadraticArc v (-D.speed) u)
  refine ⟨Cp + Cm, add_nonneg hCp hCm, ?_⟩
  filter_upwards [hp, hm] with R hpR hmR q
  have hplus := hpR q
  have hminus := hmR q
  simp only [phase_zero, sub_zero, momentAmplitude, zero_add] at hplus hminus
  have hb := (norm_sub_le _ _).trans (add_le_add hplus hminus)
  convert hb using 1
  · congr 1
    have he : Neuschel.leadingRoot 2 (-((D.speed : ℂ) * v))
        (S.phaseCoefficients 0 (Analytic.parameterShift D.shift q)) =
        -Neuschel.leadingRoot 2 ((D.speed : ℂ) * v)
          (S.phaseCoefficients 0 (Analytic.parameterShift D.shift q)) := by
      simp [Neuschel.leadingRoot, div_neg]
    rw [he, inv_neg]
    dsimp only [localMoment, halfMoment, momentAmplitude]
    simp only [Complex.ofReal_neg]
    ring
  · ring

end LocalParabolicData
end ThisWork.HigherRank.CompactSaddleFamily
