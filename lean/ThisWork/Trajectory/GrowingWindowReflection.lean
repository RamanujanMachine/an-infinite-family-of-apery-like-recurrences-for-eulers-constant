module
public import ThisWork.Trajectory.ReflectedWindowDeformation
public import ThisWork.Trajectory.GrowingTails
/-! Integrated reflection on the isolated growing saddle window. -/
@[expose] public section
namespace ThisWork.Trajectory
open Set Filter Metric MeasureTheory Analytic
open scoped Topology

theorem lower_window_neg_coordinate (f : ℂ → ℂ) (σ : ℂ) (a b c η : ℝ) :
    contourWindow .one (-σ) b a c η f =
      ∫ u in σ.re - a..σ.re + b, f (-((u : ℂ) + (η : ℂ) * Complex.I)) := by
  have h := intervalIntegral.integral_comp_neg (fun u : ℝ => f ((u : ℂ) - (η : ℂ) * Complex.I))
    (a := σ.re - a) (b := σ.re + b)
  simp only [contourWindow, Complex.neg_re]
  convert h.symm using 1
  · congr 1 <;> ring
  · apply intervalIntegral.integral_congr
    intro u _
    apply congrArg f
    push_cast
    ring

namespace ReflectedSaddleData
variable {m d : ℕ} {A₁ A₂ z : ℝ} (F : ReflectedSaddleData m d A₁ A₂ z)
    (G : GrowingContourChoice (doubleSaddleScale d A₁ A₂ z) F.windowRadius)

noncomputable def reflectionMomentFactor (k : ℕ) : ℂ := -4 * (Real.pi : ℂ) ^ 2 * (-1 : ℂ) ^ k

theorem reflectionMomentFactor_ne_zero (k : ℕ) : reflectionMomentFactor k ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact pow_ne_zero _ (by norm_num)

theorem uniform_growing_window_reflection (k : ℕ) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖contourWindow .one (-F.center n) F.data.rightWidth F.data.leftWidth
          (doubleSaddleScale d A₁ A₂ z) G.height (growingMomentKernel m d A₁ A₂ z (F.index n) k) -
        reflectionMomentFactor k * F.heightMoment n k G.height‖ ≤
        C * doubleScale m d A₁ A₂ z (F.index n) *
          Real.exp ((2 * doubleSaddleScale d A₁ A₂ z - G.rate) * sqrtScale (F.index n)) := by
  let c := doubleSaddleScale d A₁ A₂ z
  have hc : 0 < c := doubleSaddleScale_pos F.d_pos F.A₁_pos F.A₂_pos F.z_pos
  have hηc : G.height ≤ c := G.height_le hc
  have hηπ : Real.pi * G.height ≤ c := by linarith [G.height_pi]
  refine ⟨40 * (2 * c) ^ k * (F.data.leftWidth + F.data.rightWidth), by positivity [F.data.widths_pos.1, F.data.widths_pos.2], ?_⟩
  filter_upwards [F.index_tendsto.eventually (uniform_growing_reflection_error F.d_pos F.A₁_pos F.A₂_pos F.z_pos
    G.height_pos hηc hηπ (M := 2 * c) (by linarith) m),
    F.index_tendsto.eventually (eventually_reflectedScaledKernel_regular F.d_pos F.A₁_pos F.A₂_pos hc m)]
    with n herr hreg
  let a := (F.center n).re - F.data.leftWidth
  let b := (F.center n).re + F.data.rightWidth
  let R := sqrtScale (F.index n)
  let H := doubleScale m d A₁ A₂ z (F.index n)
  let p (u : ℝ) : ℂ := (u : ℂ) + (G.height : ℂ) * Complex.I
  let f (u : ℝ) : ℂ := (-p u) ^ k * kernel m d A₁ A₂ z .one (F.index n) ((R : ℂ) * (-p u))
  let g (u : ℝ) : ℂ := reflectionMomentFactor k *
    ((p u) ^ k * reflectedScaledKernel m d A₁ A₂ z (F.index n) (p u))
  have hab : a ≤ b := by dsimp only [a, b]; linarith [F.data.widths_pos.1, F.data.widths_pos.2]
  have hp (u : ℝ) (hu : u ∈ Icc a b) : p u ∈ ball (c : ℂ) (c / 4) ∧ 0 < u :=
    F.heightWindow_mem_ball G n hu
  have hnorm (u : ℝ) (hu : u ∈ Icc a b) : ‖p u‖ ≤ 2 * c := by
    have hdisk : p u ∈ saddleDisk c .three := by
      simpa only [saddleDisk, rho_three, mul_one] using ball_subset_closedBall (hp u hu).1
    exact (saddleDisk_norm_le hc .three hdisk).trans (by linarith)
  have hf : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have hK := (differentiableOn_kernel F.z_pos m d A₁ A₂ .one (F.index n)).continuousOn.comp
      (s := Icc a b) (by fun_prop : Continuous (fun u : ℝ => (R : ℂ) * (-p u))).continuousOn
      (fun u hu => by
        have h := scaled_left_mem_kernelDomain F.A₁_pos F.A₂_pos (F.index n) (sqrtScale_pos hreg.1)
          (hp u hu).2 (neg_ne_zero.mpr G.height_pos.ne')
        simpa only [p, R, neg_add_rev, Complex.ofReal_neg, neg_mul, neg_neg, add_comm] using h)
    simpa only [f, Function.comp_def, Pi.mul_def] using
      (by fun_prop : Continuous (fun u : ℝ => (-p u) ^ k)).continuousOn.mul hK
  have hg : IntervalIntegrable g volume a b := by
    have hK := (show ContinuousOn (reflectedScaledKernel m d A₁ A₂ z (F.index n))
      (ball (c : ℂ) (c / 4)) from fun s hs => (hreg.2 s hs).1.continuousAt.continuousWithinAt).comp
      (s := Icc a b) (by fun_prop : Continuous p).continuousOn (fun u hu => (hp u hu).1)
    exact (continuousOn_const.mul ((by fun_prop : Continuous (fun u : ℝ => p u ^ k)).continuousOn.mul hK)).intervalIntegrable_of_Icc hab
  rw [lower_window_neg_coordinate, heightMoment, ← intervalIntegral.integral_const_mul]
  change ‖(∫ u in a..b, f u) - ∫ u in a..b, g u‖ ≤ _
  rw [← intervalIntegral.integral_sub hf hg]
  have hbnd : ∀ u ∈ uIoc a b, ‖f u - g u‖ ≤ 40 * (2 * c) ^ k * H *
      Real.exp ((2 * c - G.rate) * R) := by
    intro u hu
    have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hu
    have he : f u - g u = (-p u) ^ k *
        (kernel m d A₁ A₂ z .one (F.index n) ((R : ℂ) * (-p u)) -
          (-4 * (Real.pi : ℂ) ^ 2 * reflectedKernel m d A₁ A₂ z (F.index n) ((R : ℂ) * (-p u)))) := by
      dsimp only [f, g, reflectedScaledKernel, reflectionMomentFactor, R]
      rw [show -((sqrtScale (F.index n) : ℂ) * p u) = (sqrtScale (F.index n) : ℂ) * (-p u) by ring]
      rw [neg_pow]
      ring
    rw [he, norm_mul, norm_pow, norm_neg]
    have h := herr (p u) (hnorm u hu') (by have hpos := (hp u hu').2; simp only [p, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]; linarith)
      (by simp [p, Complex.mul_im])
    have hrate : G.rate ≤ Real.pi * G.height / 2 :=
      (min_le_right (G.gap / 2) _).trans (min_le_left _ c)
    have hexp : Real.exp ((2 * c - Real.pi * G.height / 2) * R) ≤
        Real.exp ((2 * c - G.rate) * R) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_right hrate (sqrtScale_pos hreg.1).le])
    have hH : 0 < H := doubleScale_pos F.d_pos hreg.1 F.A₁_pos F.A₂_pos F.z_pos
    have h' := h.trans (mul_le_mul_of_nonneg_left hexp (show 0 ≤ 40 * H by positivity))
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hnorm u hu') k) h' (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  exact hi.trans_eq (by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    dsimp only [a, b]
    ring)

end ReflectedSaddleData
end ThisWork.Trajectory
