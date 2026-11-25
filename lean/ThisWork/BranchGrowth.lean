module

public import ThisWork.BoundaryVectorGrowth
public import ThisWork.CanonicalBranches
public import ThisWork.GrowthStability
public import ThisWork.BranchCenterGrowth

/-! Growth rates for actual Fourier branches and the reflected boundary mode. -/

@[expose] public section
namespace ThisWork

open Set Filter Asymptotics
open scoped Topology

theorem norm_rho (θ : ℝ) : ‖Phase.rho θ‖ = 1 := by
  simp [Phase.rho, Complex.norm_exp]

theorem rho_re_gt_neg_one {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    -1 < (Phase.rho θ).re := by
  have ha := Complex.abs_re_le_norm (Phase.rho θ)
  rw [norm_rho] at ha
  have hl : -1 ≤ (Phase.rho θ).re := (abs_le.mp ha).1
  apply lt_of_le_of_ne hl
  intro he
  have him : (Phase.rho θ).im = 0 := Complex.abs_re_eq_norm.mp (by rw [← he, norm_rho]; norm_num)
  have hs := Phase.rho_mem_slitPlane hθ
  rw [Complex.mem_slitPlane_iff] at hs
  rcases hs with h | h
  · linarith
  · exact h him

theorem rho_re_lt_one {θ : ℝ} (hθ : θ ∈ Ioo (-Real.pi) Real.pi) (hθ0 : θ ≠ 0) :
    (Phase.rho θ).re < 1 := by
  have hl := (Complex.re_le_norm (Phase.rho θ)).trans_eq (norm_rho θ)
  apply lt_of_le_of_ne hl
  intro he
  have him : (Phase.rho θ).im = 0 := Complex.abs_re_eq_norm.mp (by rw [he, norm_rho]; norm_num)
  have hp : Phase.rho θ = 1 := Complex.ext (by simpa using he) (by simpa using him)
  have hlog := congrArg Complex.im (Phase.log_rho hθ)
  rw [hp] at hlog
  apply hθ0
  simpa using hlog.symm

theorem offCut_hasLogNormGrowth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z θ : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (b : ℕ) (j : ℤ) (hθ : θ ∈ Ioo (-Real.pi) Real.pi)
    (hj : (r : ℝ) * θ = -2 * Real.pi * j) :
    HasLogNormGrowth r (commonScale r b A z)
      (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re) (branchIntegral r b A z j) := by
  obtain ⟨D⟩ := exists_offCutLocalData hr hA hz j hθ hj
  apply HasLogNormGrowth.recenter_branch hr hA hz (b := b)
  obtain ⟨C, hC, hb⟩ := D.zeroCenter_logNorm_growth hr hA hz
  refine ⟨C, hC, hb.mono (fun n hn => ⟨hn.1, ?_⟩)⟩
  have hid : Real.log ‖branchIntegral r 0 A z j n‖ - Real.log (commonScale r 0 A z n) -
      (-(r : ℝ) * saddleScale r A z * (Phase.rho θ).re) * largeScale r n =
      Real.log ‖branchIntegral r 0 A z j n‖ - Real.log (commonScale r 0 A z n) +
        largeScale r n * ((r : ℝ) * saddleScale r A z * (Phase.rho θ).re) := by ring
  rw [hid]
  exact hn.2

theorem boundary_hasLogNormGrowth {r : ℕ} (hr : 3 ≤ r)
    {A : Fin (r - 1) → ℝ} {z : ℝ} (hA : ∀ i, 0 < A i) (hz : 0 < z)
    (half : ℕ) (hrh : r = 2 * half) :
    HasLogNormGrowth r (commonScale r 0 A z) ((r : ℝ) * saddleScale r A z)
      (boundaryIntegral r 0 A z) :=
  boundary_vector_zeroCenter_growth hr hA hz half hrh

end ThisWork
