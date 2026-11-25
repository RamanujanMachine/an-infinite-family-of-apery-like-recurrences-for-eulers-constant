module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Neuschel.UniformLocal

/-! Shared analytic tools for Mellin–Barnes contour integrals. -/

@[expose] public section
namespace ThisWork

open Set Filter Metric
open scoped Topology

theorem hasDerivAt_log_scale {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : s / (c : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℂ => Complex.log (t / (c : ℂ))) (1 / s) s := by
  have h := ((hasDerivAt_id s).div_const (c : ℂ)).clog hs
  exact h.congr_deriv (by simp only [id_eq]; field_simp [Complex.ofReal_ne_zero.mpr hc.ne'])

theorem div_pos_real_mem_slitPlane_iff {c : ℝ} (hc : 0 < c) (s : ℂ) :
    s / (c : ℂ) ∈ Complex.slitPlane ↔ s ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, Complex.div_ofReal_re, Complex.div_ofReal_im,
    div_pos_iff_of_pos_right hc, ne_eq, div_eq_zero_iff, hc.ne', or_false]

end ThisWork
