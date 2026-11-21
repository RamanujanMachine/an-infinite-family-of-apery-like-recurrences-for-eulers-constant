module
public import ThisWork.Trajectory.ReflectedPhaseBounds
/-! Actual growing-kernel bounds on a fixed-height contour. -/
public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology

theorem norm_le_scale_exp_of_log_le {w : ℂ} {H r : ℝ} (hH : 0 < H)
    (h : Real.log ‖w‖ - Real.log H ≤ r) : ‖w‖ ≤ H * Real.exp r := by
  by_cases hw : w = 0
  · rw [hw, norm_zero]
    positivity
  · calc
      _ = Real.exp (Real.log ‖w‖) := (Real.exp_log (norm_pos_iff.mpr hw)).symm
      _ ≤ Real.exp (Real.log H + r) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hH]

/-- The lower edge outside the growing window has an exponential gap.
Its height is chosen before the tail cutoff, avoiding a dependence cycle. -/
theorem exists_uniform_growing_lower_gap {d : ℕ} {A₁ A₂ z δ : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hδ : 0 < δ) (m : ℕ) :
    ∃ η > 0, η ≤ doubleSaddleScale d A₁ A₂ z ∧ Real.pi * η ≤ doubleSaddleScale d A₁ A₂ z / 4 ∧
      ∃ q > 0, ∀ M : ℝ, doubleSaddleScale d A₁ A₂ z ≤ M →
        ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → -doubleSaddleScale d A₁ A₂ z ≤ s.re →
          s.im = η → δ ≤ |s.re - doubleSaddleScale d A₁ A₂ z| →
          ‖kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * (-s))‖ ≤
            doubleScale m d A₁ A₂ z n * Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - q) * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  obtain ⟨η, hη, hηc, hηπ, q, hq, hgap⟩ := reflectedPhase_horizontal_gap hc hδ
  refine ⟨η, hη, hηc, hηπ, q / 2, half_pos hq, fun M hM => ?_⟩
  filter_upwards [uniform_log_norm_branch_region hd h₁ h₂ hz (κ := c / 2) (by positivity)
    hη (half_pos hq) (by dsimp only [c]; linarith) hM m .one,
    eventually_gt_atTop (0 : ℕ)] with n hn hn₀ s hs hr hi hdist
  have hreg : η ≤ |(-s).im| := by rw [Complex.neg_im, hi, abs_neg, abs_of_pos hη]
  have hlog := hn (-s) (by simpa only [norm_neg] using hs) (Or.inr hreg)
  have hphase := hgap s hr (by rw [hi, abs_of_pos hη]) hdist
  rw [re_sqrtBranchPhase_one_neg hc (by rw [hi]; exact hη)] at hlog
  apply norm_le_scale_exp_of_log_le (doubleScale_pos hd hn₀ h₁ h₂ hz)
  have hR := sqrtScale_pos hn₀
  have h := (abs_le.mp hlog).2
  nlinarith [mul_le_mul_of_nonneg_right hphase hR.le]

theorem norm_reflected_le_four_kernel_one (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) {x : ℂ}
    (hx : x.im < 0) :
    ‖-4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n x‖ ≤
      4 * ‖kernel m d A₁ A₂ z .one n x‖ := by
  have hu : ‖Complex.exp (twist .two * x)‖ < 1 := by
    rw [norm_exp_twist_two]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (by positivity) hx)
  have hden : 1 - Complex.exp (twist .two * x) ≠ 0 := by
    intro h
    have h' := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one] at h'
    linarith
  have he := (eq_div_iff (pow_ne_zero 2 hden)).mp (kernel_one_eq_reflected m d A₁ A₂ z n hx)
  rw [← he, norm_mul, norm_pow]
  have hb := (norm_sub_le (1 : ℂ) (Complex.exp (twist .two * x)))
  rw [norm_one] at hb
  have hb₂ : ‖1 - Complex.exp (twist .two * x)‖ ≤ 2 := by linarith
  have hb₀ : 0 ≤ ‖1 - Complex.exp (twist .two * x)‖ := norm_nonneg _
  have hsq : ‖1 - Complex.exp (twist .two * x)‖ ^ 2 ≤ 4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (norm_nonneg (kernel m d A₁ A₂ z .one n x))]

/-- A uniform absolute bound on the lower growing edge, including its saddle window. -/
theorem uniform_growing_lower_bound {d : ℕ} {A₁ A₂ z η M : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hη : 0 < η)
    (hηc : η ≤ doubleSaddleScale d A₁ A₂ z) (hηπ : Real.pi * η ≤ doubleSaddleScale d A₁ A₂ z)
    (hcM : doubleSaddleScale d A₁ A₂ z ≤ M) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → -doubleSaddleScale d A₁ A₂ z ≤ s.re → s.im = η →
      ‖kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * (-s))‖ ≤ doubleScale m d A₁ A₂ z n *
        Real.exp ((2 * doubleSaddleScale d A₁ A₂ z + 3 * Real.pi * η / 2) * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  filter_upwards [uniform_log_norm_branch_region hd h₁ h₂ hz (κ := c / 2) (by positivity)
    hη (by positivity : 0 < Real.pi * η / 2) (by dsimp only [c]; linarith) hcM m .one,
    eventually_gt_atTop (0 : ℕ)] with n hn hn₀ s hs hr hi
  have hlog := hn (-s) (by simpa only [norm_neg] using hs) (Or.inr (by
    rw [Complex.neg_im, hi, abs_neg, abs_of_pos hη]))
  rw [re_sqrtBranchPhase_one_neg hc (by rw [hi]; exact hη)] at hlog
  have hphase := neg_re_sqrtPhase_horizontal_bound hc hηc hηπ hr (by rw [hi, abs_of_pos hη])
  apply norm_le_scale_exp_of_log_le (doubleScale_pos hd hn₀ h₁ h₂ hz)
  nlinarith [(abs_le.mp hlog).2, mul_le_mul_of_nonneg_right hphase (sqrtScale_pos hn₀).le]

/-- The integrated reflection error will have a strict exponential gap, even
though the absolute reflected phase increases slightly with the contour height. -/
theorem uniform_growing_reflection_error {d : ℕ} {A₁ A₂ z η M : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hη : 0 < η)
    (hηc : η ≤ doubleSaddleScale d A₁ A₂ z) (hηπ : Real.pi * η ≤ doubleSaddleScale d A₁ A₂ z)
    (hcM : doubleSaddleScale d A₁ A₂ z ≤ M) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → -doubleSaddleScale d A₁ A₂ z ≤ s.re → s.im = η →
      ‖kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * (-s)) -
          (-4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z n ((sqrtScale n : ℂ) * (-s)))‖ ≤
        40 * doubleScale m d A₁ A₂ z n *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - Real.pi * η / 2) * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  have hdecay : Tendsto (fun n => Real.exp (-2 * Real.pi * η * sqrtScale n)) atTop (𝓝 0) :=
    (Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg
      (by nlinarith [mul_pos Real.pi_pos hη] : -2 * Real.pi * η < 0) sqrtScale_tendsto))
  filter_upwards [uniform_log_norm_branch_region hd h₁ h₂ hz (κ := c / 2) (by positivity)
    hη (by positivity : 0 < Real.pi * η / 2) (by dsimp only [c]; linarith) hcM m .one,
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℕ)] with n hn hsmall hn₀ s hs hr hi
  let x := (sqrtScale n : ℂ) * (-s)
  have hx : x.im = -sqrtScale n * η := by simp [x, Complex.mul_im, hi]
  have hxneg : x.im < 0 := by rw [hx]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sqrtScale_pos hn₀)) hη
  have hexp : Real.exp (2 * Real.pi * x.im) = Real.exp (-2 * Real.pi * η * sqrtScale n) := by
    rw [hx]
    congr 1
    ring
  have herr := norm_kernel_one_sub_reflected_le m d A₁ A₂ z n hxneg (by rw [hexp]; exact hsmall.le)
  have hlog := hn (-s) (by simpa only [norm_neg] using hs) (Or.inr (by
    rw [Complex.neg_im, hi, abs_neg, abs_of_pos hη]))
  rw [re_sqrtBranchPhase_one_neg hc (by rw [hi]; exact hη)] at hlog
  have hphase := neg_re_sqrtPhase_horizontal_bound hc hηc hηπ hr (by rw [hi, abs_of_pos hη])
  have hK : ‖kernel m d A₁ A₂ z .one n x‖ ≤
      doubleScale m d A₁ A₂ z n * Real.exp ((2 * c + 3 * Real.pi * η / 2) * sqrtScale n) := by
    apply norm_le_scale_exp_of_log_le (doubleScale_pos hd hn₀ h₁ h₂ hz)
    nlinarith [(abs_le.mp hlog).2, mul_le_mul_of_nonneg_right hphase (sqrtScale_pos hn₀).le]
  have hb := (norm_reflected_le_four_kernel_one m d A₁ A₂ z n hxneg).trans
    (mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ) ≤ 4))
  calc
    _ ≤ 10 * Real.exp (2 * Real.pi * x.im) *
        (4 * (doubleScale m d A₁ A₂ z n * Real.exp ((2 * c + 3 * Real.pi * η / 2) * sqrtScale n))) :=
      herr.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = 40 * doubleScale m d A₁ A₂ z n * (Real.exp (-2 * Real.pi * η * sqrtScale n) *
        Real.exp ((2 * c + 3 * Real.pi * η / 2) * sqrtScale n)) := by rw [hexp]; ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      dsimp only [c]
      ring

end ThisWork.Trajectory
