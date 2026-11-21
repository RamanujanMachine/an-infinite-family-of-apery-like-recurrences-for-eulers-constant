module

public import ThisWork.Trajectory.Definitions
public import ThisWork.HankelPhase

/-! The square-root limiting phase at the canonical double-minimum saddle.
Its contour gap is inherited from the already proved logarithmic phase. -/

@[expose] public section

namespace ThisWork.Trajectory

open Set Filter Metric
open scoped Topology

noncomputable def sqrtScale (n : ℕ) : ℝ := (n : ℝ) ^ (1 / 2 : ℝ)

noncomputable def sqrtEquation (c : ℝ) (s : ℂ) : ℂ := 2 * Complex.log (s / (c : ℂ))

noncomputable def sqrtPhase (c : ℝ) (s : ℂ) : ℂ :=
  (2 / 3 : ℂ) * limitingPhase .three c s

theorem sqrtEquation_eq (c : ℝ) (s : ℂ) :
    sqrtEquation c s = (2 / 3 : ℂ) * limitingEquation .three c s := by
  simp [sqrtEquation, limitingEquation]
  ring

theorem sqrtScale_pos {n : ℕ} (hn : 0 < n) : 0 < sqrtScale n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem sqrtScale_tendsto : Tendsto sqrtScale atTop atTop :=
  (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp tendsto_natCast_atTop_atTop

theorem sqrtScale_sq (n : ℕ) : sqrtScale n ^ 2 = (n : ℝ) := by
  rw [sqrtScale, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

theorem hasDerivAt_sqrtPhase {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (sqrtPhase c) (sqrtEquation c s) s := by
  unfold sqrtPhase
  simpa only [sqrtEquation_eq] using
    (hasDerivAt_limitingPhase .three hc hs).const_mul (2 / 3 : ℂ)

theorem sqrtEquation_saddle {c : ℝ} (hc : 0 < c) : sqrtEquation c (c : ℂ) = 0 := by
  simp [sqrtEquation, hc.ne']

theorem sqrtPhase_saddle {c : ℝ} (hc : 0 < c) : sqrtPhase c (c : ℂ) = -2 * (c : ℂ) := by
  simp [sqrtPhase, limitingPhase, limitingEquation, hc.ne']
  ring

theorem hasDerivAt_sqrtEquation {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (sqrtEquation c) (2 / s) s := by
  unfold sqrtEquation
  simpa only [mul_one_div] using (hasDerivAt_log_scale hc hs).const_mul 2

theorem sqrtEquation_eq_zero_iff {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ Complex.slitPlane) : sqrtEquation c s = 0 ↔ s = (c : ℂ) := by
  rw [sqrtEquation_eq, mul_eq_zero]
  simpa using limitingEquation_eq_zero_iff .three hc hs

theorem log_sqrtScale {n : ℕ} (hn : 0 < n) :
    2 * Real.log (sqrtScale n) = Real.log (n : ℝ) := by
  rw [sqrtScale, Real.log_rpow (Nat.cast_pos.mpr hn)]
  ring

theorem sqrtPhase_unique_saddle {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ Complex.slitPlane) : deriv (sqrtPhase c) s = 0 ↔ s = (c : ℂ) := by
  rw [(hasDerivAt_sqrtPhase hc ((div_pos_real_mem_slitPlane_iff hc s).mpr hs)).deriv,
    sqrtEquation_eq_zero_iff hc hs]

theorem sqrtEquation_saddle_simple {c : ℝ} (hc : 0 < c) :
    deriv (sqrtEquation c) (c : ℂ) ≠ 0 := by
  rw [(hasDerivAt_sqrtEquation hc (by simp [hc.ne', Complex.one_mem_slitPlane])).deriv]
  exact div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hc.ne')

/-- A global strict phase gap on the same polygonal Hankel contour as before. -/
theorem sqrtPhase_hankel_gap {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s ∈ Analytic.hankelTrace c c) (hne : s ≠ (c : ℂ)) :
    (sqrtPhase c s).re < -2 * c := by
  have h := Analytic.hankel_phase_gap_three hc hs (by simpa using hne)
  simp [sqrtPhase, Complex.mul_re]
  linarith

end ThisWork.Trajectory
