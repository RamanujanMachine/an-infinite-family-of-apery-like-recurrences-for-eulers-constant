module
public import ThisWork.Trajectory.ReflectedKernelNorm
public import ThisWork.Trajectory.KernelConjugation
/-! A fixed contour height selected from the reflected phase gap. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

structure GrowingContourChoice (c δ : ℝ) where
  height : ℝ
  height_pos : 0 < height
  height_small : height ≤ c / 32
  height_pi : Real.pi * height ≤ c / 4
  gap : ℝ
  gap_pos : 0 < gap
  phase_gap : ∀ s : ℂ, -c ≤ s.re → |s.im| ≤ height → δ ≤ |s.re - c| →
    -(sqrtPhase c s).re ≤ 2 * c - gap

theorem exists_growingContourChoice {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Nonempty (GrowingContourChoice c δ) := by
  obtain ⟨η, hη, _, hηπ, q, hq, hg⟩ := reflectedPhase_horizontal_gap hc hδ
  refine ⟨⟨min η (c / 32), lt_min hη (by positivity), min_le_right _ _, ?_, q, hq, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_left η (c / 32)) Real.pi_pos.le).trans hηπ
  · intro s hr hi hd
    exact hg s hr (hi.trans (min_le_left _ _)) hd

namespace GrowingContourChoice
variable {c δ : ℝ} (G : GrowingContourChoice c δ)

theorem height_le (hc : 0 < c) : G.height ≤ c := by linarith [G.height_small]

noncomputable def rate : ℝ := min (G.gap / 2) (min (Real.pi * G.height / 2) c)

theorem rate_pos (hc : 0 < c) : 0 < G.rate :=
  lt_min (half_pos G.gap_pos) (lt_min (by positivity [G.height_pos]) hc)

theorem uniform_lower_gap {d : ℕ} {A₁ A₂ z M : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z)
    (hc : c = doubleSaddleScale d A₁ A₂ z) (hM : c ≤ M) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → -c ≤ s.re → s.im = G.height → δ ≤ |s.re - c| →
      ‖kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * (-s))‖ ≤
        doubleScale m d A₁ A₂ z n * Real.exp ((2 * c - G.rate) * sqrtScale n) := by
  have hc₀ : 0 < c := hc ▸ doubleSaddleScale_pos hd h₁ h₂ hz
  filter_upwards [uniform_log_norm_branch_region hd h₁ h₂ hz (κ := c / 2) (by positivity)
    G.height_pos (half_pos G.gap_pos) (by rw [← hc]; linarith) (by simpa only [← hc] using hM) m .one,
    eventually_gt_atTop (0 : ℕ)] with n hn hn₀ s hs hr hi hd'
  have hlog := hn (-s) (by simpa only [norm_neg] using hs) (Or.inr (by
    rw [Complex.neg_im, hi, abs_neg, abs_of_pos G.height_pos]))
  rw [← hc, re_sqrtBranchPhase_one_neg hc₀ (by rw [hi]; exact G.height_pos)] at hlog
  have hp := G.phase_gap s hr (by rw [hi, abs_of_pos G.height_pos]) hd'
  apply norm_le_scale_exp_of_log_le (doubleScale_pos hd hn₀ h₁ h₂ hz)
  have he : G.rate ≤ G.gap / 2 := min_le_left _ _
  nlinarith [(abs_le.mp hlog).2, mul_le_mul_of_nonneg_right hp (sqrtScale_pos hn₀).le,
    mul_le_mul_of_nonneg_right he (sqrtScale_pos hn₀).le]

end GrowingContourChoice

namespace ReflectedSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)

noncomputable def windowRadius : ℝ := min F.data.leftWidth F.data.rightWidth / 4

theorem windowRadius_pos : 0 < F.windowRadius :=
  div_pos (lt_min F.data.widths_pos.1 F.data.widths_pos.2) (by norm_num)

theorem exists_contourChoice : Nonempty (GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius) :=
  exists_growingContourChoice (doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos) F.windowRadius_pos

theorem center_tendsto : Tendsto F.center atTop (𝓝 (doubleSaddleScale d A₁ A₂ z : ℂ)) := by
  change Tendsto (fun n : ℕ => F.family.saddle (n + F.data.shift)) atTop
    (𝓝 (doubleSaddleScale d A₁ A₂ z : ℂ))
  simpa only [F.family.saddle_limit, Function.comp_def] using
    ((OnePoint.continuous_iff_from_nat F.family.saddle).mp F.family.saddle.continuous).comp
      (tendsto_add_atTop_nat F.data.shift)

theorem eventually_center_displacement_lt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ‖F.center n - (doubleSaddleScale d A₁ A₂ z : ℂ)‖ < r := by
  simpa only [mem_ball, dist_eq_norm] using F.center_tendsto.eventually (ball_mem_nhds _ hr)

end ReflectedSaddleData
end ThisWork.Trajectory
