module
public import ThisWork.QuadraticSaddleMoments
public import ThisWork.LocalWindowIdentity
/-! Fixed straight windows for generic Gaussian moments. -/
@[expose] public section
namespace ThisWork.Analytic.QuadraticSaddleFamily.LocalSaddleData
open Set MeasureTheory Filter Metric
open scoped Topology OnePoint

theorem localMoment_eq_window {S : QuadraticSaddleFamily} (D : S.LocalSaddleData)
    (R : ℝ) (k : ℕ) (w : OnePoint ℕ) :
    D.localMoment R k w = ∫ t in -D.leftWidth..D.rightWidth, S.tangent *
      (Complex.exp (-(R : ℂ) * S.phase ((t : ℂ) * S.tangent) (parameterShift D.shift w)) *
        (((t : ℂ) * S.tangent + S.saddle (parameterShift D.shift w)) ^ k)) := by
  have hp := (S.differentiableOn_phase (parameterShift D.shift w)).continuousOn
  have hf : ContinuousOn (fun t =>
      Complex.exp (-(R : ℂ) * S.phase t (parameterShift D.shift w)) *
        (t + S.saddle (parameterShift D.shift w)) ^ k) (ball 0 S.radius) :=
    (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hp)).mul
      ((continuous_id.add continuous_const).pow k).continuousOn
  simpa only [localMoment, velocity, momentAmplitude, leftWidth, rightWidth] using
    two_sided_rayIntegral_eq_window_of_ball S.norm_tangent D.speed_pos.le
      D.positive.cutoff_mem.1.le D.negative.cutoff_mem.1.le D.widths_lt.2 D.widths_lt.1 hf

theorem normalizedLocalMoment_tendsto {S : QuadraticSaddleFamily} (D : S.LocalSaddleData)
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (k : ℕ) :
    Tendsto (fun n => D.normalizedLocalMoment (R n) k n) atTop
      (𝓝 (S.saddle ∞ ^ k)) := by
  have hσ : Tendsto (fun n : ℕ => S.saddle (parameterShift D.shift n)) atTop
      (𝓝 (S.saddle ∞)) := by
    simpa only [parameterShift_nat, Function.comp_def] using
      ((OnePoint.continuous_iff_from_nat S.saddle).mp S.saddle.continuous).comp
        (tendsto_add_atTop_nat D.shift)
  obtain ⟨C, _, hc⟩ := D.normalized_local_moment_error k
  have he : Tendsto (fun n => D.normalizedLocalMoment (R n) k n -
      S.saddle (parameterShift D.shift n) ^ k) atTop (𝓝 0) :=
    squeeze_zero_norm' ((hR.eventually hc).mono (fun n hn => hn n))
      (by simpa only [mul_zero, Function.comp_def] using
        ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp hR).const_mul C)
  simpa only [sub_add_cancel, zero_add] using he.add (hσ.pow k)

end ThisWork.Analytic.QuadraticSaddleFamily.LocalSaddleData
