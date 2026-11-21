module
public import ThisWork.Trajectory.GrowingContourBounds
/-! Conjugation and suppression of the upper edge for the first branch. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric Analytic
open scoped Topology ComplexConjugate

theorem kernel_three_conj (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (x : ℂ) :
    kernel m d A₁ A₂ z .three n (conj x) = conj (kernel m d A₁ A₂ z .three n x) := by
  simp only [kernel, twist_three, zero_mul, Complex.exp_zero, mul_one,
    map_mul, map_pow, ← Complex.Gamma_conj, ← Complex.exp_conj,
    map_add, map_sub, map_one, map_natCast, Complex.conj_ofReal]

theorem norm_kernel_one_conj (m d : ℕ) (A₁ A₂ z : ℝ) (n : ℕ) (x : ℂ) :
    ‖kernel m d A₁ A₂ z .one n (conj x)‖ =
      ‖kernel m d A₁ A₂ z .one n x‖ * Real.exp (4 * Real.pi * x.im) := by
  rw [kernel_eq_twist m d A₁ A₂ z .one n (conj x), kernel_eq_twist m d A₁ A₂ z .one n x,
    norm_mul, norm_mul, kernel_three_conj, Complex.norm_conj]
  have he (w : ℂ) : ‖Complex.exp (twist .one * w)‖ = Real.exp (-2 * Real.pi * w.im) := by
    simp [twist_one, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [he, he, Complex.conj_im]
  simp only [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  ring

theorem uniform_growing_upper_bound {d : ℕ} {A₁ A₂ z η M : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hη : 0 < η)
    (hηc : η ≤ doubleSaddleScale d A₁ A₂ z) (hηπ : Real.pi * η ≤ doubleSaddleScale d A₁ A₂ z)
    (hcM : doubleSaddleScale d A₁ A₂ z ≤ M) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, ‖s‖ ≤ M → -doubleSaddleScale d A₁ A₂ z ≤ s.re → s.im = η →
      ‖kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * (-conj s))‖ ≤ doubleScale m d A₁ A₂ z n *
        Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - 5 * Real.pi * η / 2) * sqrtScale n) := by
  filter_upwards [uniform_growing_lower_bound hd h₁ h₂ hz hη hηc hηπ hcM m] with n hn s hs hr hi
  have he : (sqrtScale n : ℂ) * (-conj s) = conj ((sqrtScale n : ℂ) * (-s)) := by
    simp only [map_mul, map_neg, Complex.conj_ofReal]
  rw [he, norm_kernel_one_conj]
  have hx : ((sqrtScale n : ℂ) * (-s)).im = -sqrtScale n * η := by
    simp [Complex.mul_im, hi]
  calc
    _ ≤ (doubleScale m d A₁ A₂ z n *
        Real.exp ((2 * doubleSaddleScale d A₁ A₂ z + 3 * Real.pi * η / 2) * sqrtScale n)) *
          Real.exp (4 * Real.pi * ((sqrtScale n : ℂ) * (-s)).im) :=
      mul_le_mul_of_nonneg_right (hn s hs hr hi) (Real.exp_pos _).le
    _ = _ := by
      rw [hx, mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem re_sqrtPhase_right_le {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hr : s.re = c) (hi : |s.im| ≤ c) : (sqrtPhase c s).re ≤ -2 * c := by
  by_cases hs : s = (c : ℂ)
  · rw [hs, sqrtPhase_saddle hc]
    simp
  · apply (sqrtPhase_hankel_gap hc ?_ hs).le
    apply Or.inl
    apply Or.inr
    refine ⟨s.im, ⟨?_, ?_⟩, ?_⟩
    · linarith [(abs_le.mp hi).1]
    · exact (abs_le.mp hi).2
    · apply Complex.ext <;> simp [hr, Complex.mul_re, Complex.mul_im]

/-- The right vertical edge is uniformly separated from the growing saddle. -/
theorem uniform_growing_right_bound {d : ℕ} {A₁ A₂ z η : ℝ}
    (hd : 0 < d) (h₁ : 0 < A₁) (h₂ : 0 < A₂) (hz : 0 < z) (hη : 0 < η)
    (hηc : η ≤ doubleSaddleScale d A₁ A₂ z)
    (hηπ : Real.pi * η ≤ doubleSaddleScale d A₁ A₂ z / 4) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℂ, s.re = doubleSaddleScale d A₁ A₂ z → |s.im| ≤ η →
      ‖kernel m d A₁ A₂ z .one n ((sqrtScale n : ℂ) * s)‖ ≤
        doubleScale m d A₁ A₂ z n * Real.exp (-doubleSaddleScale d A₁ A₂ z * sqrtScale n) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos hd h₁ h₂ hz
  filter_upwards [uniform_log_norm_branch_region hd h₁ h₂ hz (κ := c / 2) (by positivity)
    hη (half_pos hc) (by dsimp only [c]; linarith) (M := 2 * c) (by dsimp only [c]; linarith) m .one,
    eventually_gt_atTop (0 : ℕ)] with n hn hn₀ s hr hi
  have hsM : ‖s‖ ≤ 2 * c := (Complex.norm_le_abs_re_add_abs_im s).trans (by
    rw [hr, abs_of_pos hc]
    linarith)
  have hlog := hn s hsM (Or.inl (by rw [hr]; linarith))
  have hp := re_sqrtPhase_right_le hc hr (hi.trans hηc)
  have he : (sqrtBranchPhase .one c s).re = (sqrtPhase c s).re - 2 * Real.pi * s.im := by
    simp [sqrtBranchPhase, twist_one, Complex.mul_re, Complex.mul_im]
    ring
  rw [he] at hlog
  apply norm_le_scale_exp_of_log_le (doubleScale_pos hd hn₀ h₁ h₂ hz)
  have hheight : -2 * Real.pi * s.im ≤ 2 * Real.pi * η := by
    nlinarith [(abs_le.mp hi).1, Real.pi_pos]
  have hphase : (sqrtPhase c s).re - 2 * Real.pi * s.im ≤ -3 * c / 2 := by linarith
  nlinarith [(abs_le.mp hlog).2, mul_le_mul_of_nonneg_right hphase (sqrtScale_pos hn₀).le]

end ThisWork.Trajectory
